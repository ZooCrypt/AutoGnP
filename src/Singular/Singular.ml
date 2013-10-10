open Type
open Expr
open Poly
open Util
open SingLexer

module F = Format

(* Singular field expression *)
type fexp =
    V of int
  | SOne
  | SZ
  | SOpp of fexp
  | SInv of fexp
  | SPlus of fexp * fexp
  | SMult of fexp * fexp

(* pretty-printer function for already abstracted field expression *)
let rec string_of_fexp e = match e with
  | V i        -> F.sprintf "x%i" i
  | SOne       -> "1"
  | SZ         -> "0"
  | SOpp(a)    -> F.sprintf "-(%s)" (string_of_fexp a)
  | SInv(a)    -> F.sprintf "1/(%s)" (string_of_fexp a)
  | SPlus(a,b) -> F.sprintf "(%s + %s)" (string_of_fexp a) (string_of_fexp b)
  | SMult(a,b) -> F.sprintf "(%s * %s)" (string_of_fexp a) (string_of_fexp b)

(* Abstraction of 'Expr.expr' to sfexp *)
let abstract_non_field e0 =
  let i = ref 0 in
  let bindings = ref [] in
  let lookup k = match massoc k !bindings with
    | None   -> incr i; bindings := (k,!i)::!bindings; !i
    | Some j -> j
  in
  let rec go e = match e.e_node with
    | Cnst FOne              -> SOne
    | Cnst FZ                -> SZ
    | App (FOpp,[a])         -> SOpp(go a)
    | App (FInv,[a])         -> SInv(go a)
    | App (FMinus,[a;b])     -> SPlus(go a, SOpp (go b))
    | App (FDiv,[a;b])       -> SMult(go a, SInv (go b))
    | Nary (FPlus, a::es)       -> List.fold_left (fun acc e -> SPlus(acc, go e)) (go a) es
    | Nary (FMult, a::es)       -> List.fold_left (fun acc e -> SMult(acc, go e)) (go a) es
    | _ -> V (lookup e)
  in
  let se = go e0 in
  (se, List.map swap !bindings)


(** Parser for Singular Polynomials in Q[x1,..,xk] *)

(* for debugging / error messages *)
let string_of_token t = match t with
  | INT i -> F.sprintf "INT %i" i
  | VAR i -> F.sprintf "VAR %i" i
  | PLUS  -> "PLUS"
  | MINUS -> "MINUS"
  | TIMES -> "TIMES"
  | POW   -> "PLUS"
  | DIV   -> "DIV"
  | OPEN  -> "OPEN"
  | CLOSE -> "CLOSE"
  | EOF   -> "EOF"

let string_of_tokens ts = String.concat ", " (List.map string_of_token ts)

let lex_to_list lexer s =
  let lb = Lexing.from_string s in
  let rec go () = match lexer lb with
    | EOF -> []
    | t   -> t :: go ()
  in go ()

(* Parse singular result into Poly.poly data type.
   We don't have nesting, so we use a custom parser. *)
let parse_poly s =
  let rec pterm toks poly coeff mon  = match toks with
    | OPEN::rest                  -> pterm rest poly coeff mon
    | INT i::rest                 -> psep  rest poly (coeff*i) []
    | (VAR i)::POW::(INT j)::rest -> psep  rest poly coeff (mon@[(i,j)])
    | (VAR i)::rest               -> psep  rest poly coeff (mon@[(i,1)])
    | MINUS::rest                 -> pterm rest poly (coeff * (0)) mon
    | _                           ->
      failwith ("Singular.parse_poly: pmonom expected var or var^int, got "
                ^ string_of_tokens toks)
  and psep toks poly coeff mon = match toks with
    | TIMES::rest                        -> pterm rest poly coeff mon
    | PLUS::rest                         -> pterm rest (poly@[(coeff,mon)]) (-1) []
    | MINUS::rest                        -> pterm rest (poly@[(coeff,mon)]) (-1) []
    | CLOSE::[]                          -> poly@[(coeff,mon)]
    | []                                 -> poly@[(coeff,mon)]
    | _                                  ->
      failwith ("Singular.parse_poly: psep expected *, +, or ), got "
                ^ string_of_tokens toks)
  in pterm (lex_to_list SingLexer.lex s) [] 1 []

(** Abstraction of non-field expression with variables *)

(** Using Singular to perform polynomial computations *)

let singular_command = F.sprintf "Singular -q -t"

let call_singular cmd =
  (* F.printf "singular command: `%s'\n\n" singular_command; *)
  let (c_in, c_out) = Unix.open_process singular_command in
  output_string c_out cmd;
  (* F.printf "singular input: `%s' has been sent\n\n" cmd; *)
  flush_all ();
  let rec loop o =
    try
      let l = input_line c_in in
      (* F.printf "singular output: `%s'\n" l; *)
      loop (o @ [l])
    with End_of_file ->
      ignore (Unix.close_process (c_in,c_out));
      o
  in loop []

let norm e =
  let (se,bindings) = abstract_non_field e in
  let vars = List.map (fun x -> F.sprintf "x%i" (fst x)) bindings in
  let var_string = String.concat "," vars in
  let cmd = F.sprintf "LIB \"poly.lib\";ring R = (0,%s),(a),dp;\n\
                       number f = %s;\nnumerator(f);denominator(f);quit;\n"
                      var_string
                      (string_of_fexp se)
  in

  let import s = term_of_poly bindings (parse_poly s) in
  match call_singular cmd with
  | [ snum; sdenom ] ->
      let num   = import snum  in
      let denom = import sdenom in
      (* F.printf "num: %a\ndenom: %a\n" pp_exp num pp_exp denom; *)
      if e_equal denom mk_FOne then num
      else mk_FDiv num denom
  | repls ->
      failwith (F.sprintf "Singular.norm: unexpected result %s\n"
                  (String.concat "\n" repls))