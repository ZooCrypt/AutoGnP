open Type
open Expr
open Poly
open Util
open SingLexer

module F = Format

(** Singular pretty printer for field expressions *)

(* pretty-printer function for already abstracted field expression *)
let pp_expr_sing fmt t = assert false
(* 
  let rec go rparens t = match t with
  | V v             -> F.fprintf fmt "%a%" Vsym.pp v
  | App (FMinus,[a]) -> parens (string "- " ^^ (parens  (go false a)))
  | App (Inv,[a])   -> parens (string "1 / " ^^ (parens  (go false a)))
  | Const Zero      -> string "0"
  | Const One       -> string "1"
  | Const _         -> failwith "Singular cannot understand Const"
  | Proj (_,_)      -> failwith "Singular cannot understand Proj"
  | Tuple _         -> failwith "Singular cannot understand Tuple"
  | App (_,_)       -> failwith "Singular cannot understand this App"
  | NaryApp (o,ts) when o = Sum || o = Prod ->
     group (parens_maybe rparens (go_terms true (space ^^ pp_nop o) ts))
  | NaryApp (_,_)   -> failwith "Singular cannot understand this NaryApp"
  and go_terms rparens sep ts =
    separate (sep ^^ break 1) (List.map (go rparens) ts)
  in go false t
 *)

let string_of_term_sing e = assert false

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

(* PRE: expects an expression of type Zq *)
let abstract_non_field t =
  let bindings = ref (0,[]) in
  let addBinding (t : Expr.expr) ty = match massoc t (snd !bindings) with
    | None   -> let (i,(bs : (Expr.expr * (string * ty)) list)) = !bindings in
                let i = i+1 in
                let xi = F.sprintf "x%i" i in
                let () = bindings := (i,(t,(xi,ty))::bs) in
                (xi,ty)
    | Some i -> i
  in
  let rec go e = match e.e_node with
    | _ -> assert false (*
    | App (o,[a]) when o = Minus || o = Inv -> App (o,[go a])
    | Const Zero | Const One -> t
    | NaryApp (o,ts) when o = Sum || o = Prod ->
        NaryApp (o, List.map go ts)
    | t -> let xi = addBinding t Zq in R(xi) *)
  in
  let t' = go t in (t', List.map swap (snd !bindings))

let subst_binding bindings t = assert false
(*  let substR v = match massoc v bindings with
    | Some t -> t
    | None   ->
        failwith (sprintf "Singular.subst_binding_field: unknown variable: %s in %s"
                    (fst v)
                    (String.concat "," (List.map (fun x -> fst (fst x)) bindings)))
  in fold_term_simp ~fR:substR t *)

(** Using Singular to perform polynomial computations *)

let singular_command = F.sprintf "/Users/beschmi/bin/Singular -q -t"

let call_singular cmd =
  (* debug (sprintf "singular command: `%s'\n\n" singular_command); *)
  let (c_in, c_out) = Unix.open_process singular_command in
  output_string c_out cmd;
  (* debug (sprintf "singular input: `%s' has been sent\n\n" cmd); *)
  flush_all ();
  let rec loop o =
    try
      let l = input_line c_in in
      (* debug (sprintf "singular output: `%s'\n" l); *)
      loop (o @ [l])
    with End_of_file ->
      ignore (Unix.close_process (c_in,c_out));
      o
  in loop []

let norm t0 =
  let (t,bindings) = abstract_non_field t0 in
  let vars = List.sort compare (List.map (fun x -> fst (fst x)) bindings) in
  let var_string = String.concat "," vars in
  let cmd = F.sprintf "LIB \"poly.lib\";ring r2 = (0,%s),(a),dp;\n\
                       number f = %s;\nnumerator(f);denominator(f);quit;\n"
                      var_string
                      (string_of_term_sing t)
  in
  let import s = subst_binding bindings (term_of_poly (parse_poly s)) in
  match call_singular cmd with
    | [ snum; sdenom ] ->
        let num   = import snum  in
        let denom = import sdenom in
        (* debug (sprintf "num: %s\ndenom: %s\n" (string_of_term num) (string_of_term denom)); *)
        if e_equal denom mk_FOne then num
        else mk_FMult [num; mk_FInv denom]
    | repls          ->
        failwith (F.sprintf "Singular.norm: unexpected result %s\n"
                    (String.concat "\n" repls))

let main () =
  let vs = Vsym.mk "x" mk_Fq in
  let v = mk_V vs in
  let e = mk_FDiv v v in 
  let (e',bindings) = abstract_non_field e in
  F.printf "%a\n" pp_exp e';
  print_newline ();
  F.printf "%a\n" pp_exp (subst_binding bindings e')