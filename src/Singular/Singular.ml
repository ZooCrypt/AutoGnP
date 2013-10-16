open Expr
open Poly
open SingLexer
open Util

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
let rec rename hr = function 
  | V i -> V (Hashtbl.find hr i)
  | (SOne | SZ) as e -> e
  | SOpp e -> SOpp (rename hr e)
  | SInv e -> SInv (rename hr e)
  | SPlus(e1,e2) -> SPlus (rename hr e1, rename hr e2)
  | SMult(e1,e2) -> SMult (rename hr e1, rename hr e2)

let norm_i = ref 0

let trace = ref []

let abstract_non_field before e0 =
  let c = ref 0 in
  let he = He.create 17 in
  let lookup e =
    try He.find he e 
    with Not_found ->
      let n = !c in
      incr c;
      He.add he e n;
      n in
  let rec go e = 
    let e = before e in
    match e.e_node with
    | Cnst FOne           -> SOne
    | Cnst FZ             -> SZ
    | App (FOpp,[a])      -> SOpp(go a)
    | App (FInv,[a])      -> SInv(go a)
    | App (FMinus,[a;b])  -> SPlus(go a, SOpp (go b))
    | App (FDiv,[a;b])    -> SMult(go a, SInv (go b))
    | Nary (FPlus, a::es) -> 
      List.fold_left (fun acc e -> SPlus(acc, go e)) (go a) es
    | Nary (FMult, a::es) -> 
      List.fold_left (fun acc e -> SMult(acc, go e)) (go a) es
    | _ -> V (lookup e)
  in
  let se = go e0 in
  let binding = List.sort e_compare (He.fold (fun e _ l -> e::l) he []) in
  let hr = Hashtbl.create 17 in
  let hv = Hashtbl.create 17 in
  let c = ref 0 in
  List.iter (fun e -> let i = !c in incr c;
                      trace := (!norm_i, true,
                                (if is_GTLog e then (fsprintf "%a" pp_exp e |> fsget) else ""),
                                i, e.e_tag,
                                if is_GTLog e then true else false)::!trace;
                      Hashtbl.add hr (He.find he e) i;
                      Hashtbl.add hv i e) binding;
  (rename hr se, !c, hv)

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
    | MINUS::rest                 -> pterm rest poly (coeff * (-1)) mon
    | _                           ->
      failwith ("Singular.parse_poly: pmonom expected var or var^int, got "
                ^ string_of_tokens toks)
  and psep toks poly coeff mon = match toks with
    | TIMES::rest -> pterm rest poly coeff mon
    | PLUS::rest  -> pterm rest (poly@[(coeff,mon)]) 1    []
    | MINUS::rest -> pterm rest (poly@[(coeff,mon)]) (-1) []
    | CLOSE::[]   -> poly@[(coeff,mon)]
    | []          -> poly@[(coeff,mon)]
    | _           ->
      failwith ("Singular.parse_poly: psep expected *, +, or ), got "
                ^ string_of_tokens toks)
  in pterm (lex_to_list SingLexer.lex s) [] 1 []

(** Abstraction of non-field expression with variables *)

(** Using Singular to perform polynomial computations *)

let singular_command = F.sprintf "Singular -q -t"

let singular_chans = ref None

let call_singular cmd linenum =
  (* F.printf "singular command: `%s'\n\n" singular_command; *)
  let (c_in, c_out) =
    match !singular_chans with
    | None ->
        let cs = Unix.open_process singular_command in
        output_string (snd cs) "LIB \"poly.lib\"; ring R = (0,x0),(a),dp;";
        singular_chans := Some cs;
        cs
    | Some cs -> cs
  in
  output_string c_out cmd;
  (* F.printf "singular input: `%s' has been sent\n\n" cmd; *)
  flush c_out;
  let rec loop o linenum =
    if linenum = 0 then o
    else (
      try
        let l = input_line c_in in
        (* F.printf "singular output: `%s'\n" l; *)
        loop (o @ [l]) (linenum - 1)
      with End_of_file ->
        ignore (Unix.close_process (c_in,c_out)); (* FIXME: close on exit *)
        o)
  in loop [] linenum

let print_trace () =
  List.iter (fun (i,binding,s,j,tag,islog) ->
               if not binding then
                 Format.fprintf Format.err_formatter "%i: output%s\n%!" i s
               else
                 Format.fprintf Format.err_formatter "%i: binding %i |-> %b,%i,%s\n%!" i j islog tag s)
            (List.rev !trace)

let norm before e =
  incr norm_i;
  let (se,c,hv) = abstract_non_field before e in
  let vars = Array.to_list (Array.init c (F.sprintf "x%i")) in
  let var_string = String.concat "," (if vars = [] then ["x1"] else vars) in
  let cmd = F.sprintf "ring R = (0,%s),(a),dp;\n\
                       number f = %s;\nnumerator(f);denominator(f);\n"
                      var_string
                      (string_of_fexp se)
  in
  Gc.compact (); (* note that if this is commented out, Test_Proof_BB1.ml fails *)
  let import s = term_of_poly hv (parse_poly s) in
  match call_singular cmd 3 with
  | [ _; snum; sdenom ] -> (* ring redeclared is first reply *)
      trace := (!norm_i,false, String.copy snum, 0,0,false) :: !trace;

      let num   = import snum  in
      let denom = import sdenom in
      (* F.printf "num: %a\ndenom: %a\n" pp_exp num pp_exp denom; *)
      if e_equal denom mk_FOne then num
      else mk_FDiv num denom
  | repls ->
      failwith (F.sprintf "Singular.norm: unexpected result %s\n"
                  (String.concat "\n" repls))
