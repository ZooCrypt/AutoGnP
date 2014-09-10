(*s Using CAS to perform computations on polynomials *)

(*i*)
open Expr
open Poly
open Util
open CASLexer

module Ht = Hashtbl
module YS = Yojson.Safe
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Pure field expressions without other operators} *)

(** Field expression. *)
type fexp =
    SV of int
  | SNat of int
  | SOpp of fexp
  | SInv of fexp
  | SPlus of fexp * fexp
  | SMult of fexp * fexp

(** Pretty-printer function for already abstracted field expression. *)
let rec string_of_fexp e = match e with
  | SV i       -> F.sprintf "x%i" i
  | SNat(n)    -> F.sprintf "%i" n
  | SOpp(a)    -> F.sprintf "-(%s)" (string_of_fexp a)
  | SInv(a)    -> F.sprintf "1/(%s)" (string_of_fexp a)
  | SPlus(a,b) -> F.sprintf "(%s + %s)" (string_of_fexp a) (string_of_fexp b)
  | SMult(a,b) -> F.sprintf "(%s * %s)" (string_of_fexp a) (string_of_fexp b)

(** Abstraction of [Expr.expr] to [sfexp]. *)
let rec rename hr = function 
  | SV i -> SV (Ht.find hr i)
  | (SNat _) as e -> e
  | SOpp e -> SOpp (rename hr e)
  | SInv e -> SInv (rename hr e)
  | SPlus(e1,e2) -> SPlus (rename hr e1, rename hr e2)
  | SMult(e1,e2) -> SMult (rename hr e1, rename hr e2)

(** [abstract_non_field_multiple before es] abstracts all
    expressions in [es] at once sharing variables for
    common non-field subexpression. It also applies the
    [before] function to expressions beforehand. *)
let abstract_non_field_multiple before es =
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
    | Cnst (FNat n)       -> SNat n
    | App (FOpp,[a])      -> SOpp(go a)
    | App (FInv,[a])      -> SInv(go a)
    | App (FMinus,[a;b])  -> SPlus(go a, SOpp (go b))
    | App (FDiv,[a;b])    -> SMult(go a, SInv (go b))
    | Nary (FPlus, a::es) -> 
      List.fold_left (fun acc e -> SPlus(acc, go e)) (go a) es
    | Nary (FMult, a::es) -> 
      List.fold_left (fun acc e -> SMult(acc, go e)) (go a) es
    | _ -> SV (lookup e)
  in
  let ses = List.map go es in
  let binding = List.sort e_compare (He.fold (fun e _ l -> e::l) he []) in
  let hr = Ht.create 17 in
  let hv = Ht.create 17 in
  let c = ref 0 in
  List.iter (fun e -> let i = !c in incr c;
                      Ht.add hr (He.find he e) i;
                      Ht.add hv i e) binding;
  (List.map (rename hr) ses, !c, hv)

(** See [abstract_non_field] *)
let abstract_non_field before e =
  match abstract_non_field_multiple before [e] with
  | ([e],c,hv) -> (e,c,hv)
  | _ -> assert false

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Parser for Singular Polynomials in $Q[x_1,..,x_k]$} *)

(*i*)
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
(*i*)

let lex_to_list lexer s =
  let lb = Lexing.from_string s in
  let rec go () = match lexer lb with
    | EOF -> []
    | t   -> t :: go ()
  in go ()

(** Parse CAS result into [Poly.poly] data type.
    We do not have nesting, so we use a custom parser. *)
let parse_poly s =
  let rec pterm toks poly coeff mon  = match toks with
    | OPEN::rest                  -> pterm rest poly coeff mon
    | INT i::rest                 -> psep  rest poly (coeff*i) []
    | (VAR i)::POW::(INT j)::rest -> psep  rest poly coeff (mon@[(i,j)])
    | (VAR i)::rest               -> psep  rest poly coeff (mon@[(i,1)])
    | MINUS::rest                 -> pterm rest poly (coeff * (-1)) mon
    | _                           ->
      failwith ("parse_poly: pmonom expected var or var^int, got "
                ^ string_of_tokens toks)
  and psep toks poly coeff mon = match toks with
    | TIMES::rest -> pterm rest poly coeff mon
    | PLUS::rest  -> pterm rest (poly@[(coeff,mon)]) 1    []
    | MINUS::rest -> pterm rest (poly@[(coeff,mon)]) (-1) []
    | CLOSE::[]   -> poly@[(coeff,mon)]
    | []          -> poly@[(coeff,mon)]
    | _           ->
      failwith ("parse_poly: psep expected *, +, or ), got "
                ^ string_of_tokens toks)
  in pterm (lex_to_list CASLexer.lex s) [] 1 []

let parse_poly_json l =
  List.map (fun s ->
              match s with
              | `List [`Int c; `List m] ->
                (c, List.map (function `List [`Int v; `Int e] -> (v,e) | _ -> failwith "error") m)
              | _ -> failwith "error") l

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Using CAS to perform polynomial computations} *)

type systems = Singular | Macaulay | Sage

let ht_systems = Ht.create 17

let setup_systems =
  [ (Singular,
     ("Singular -q -t", Some("LIB \"poly.lib\"; ring R = (0,x0),(a),dp; number n = 0; poly f = 0; ideal I = 0;")))
  ; (Macaulay, ("m2 --no-tvalues --no-tty --no-prompts --silent", None))
  ; (Sage, ("scripts/zoocrypt_sage.py", None)) ]

let is_started sys =
  try ignore (Ht.find ht_systems sys); true
  with Not_found -> false

let call_system sys cmd linenum =
  let (c_in, c_out) =
    try Ht.find ht_systems sys
    with Not_found ->
        let (command,setup) = List.assoc sys setup_systems in
        let cs = Unix.open_process command in
        (match setup with Some s -> output_string (snd cs) s | _ -> ());
        Ht.add ht_systems sys cs;
        cs
  in
  output_string c_out cmd;
  (*i F.printf "input: `%s' has been sent\n\n%!" cmd; i*)
  flush c_out;
  let rec loop o linenum =
    if linenum = 0 then o
    else (
      try
        let l = input_line c_in in
        (*i F.printf "output: `%s'\n%!" l; i*)
        loop (o @ [l]) (linenum - 1)
      with End_of_file ->
        ignore (Unix.close_process (c_in,c_out)); (* FIXME: close on exit *)
        o)
  in loop [] linenum

let import_poly (caller : string) poly (hv : (int, expr) Ht.t) =
  exp_of_poly
    (map_poly
       (fun i ->
          try Ht.find hv i
          with Not_found ->
            failwith ("invalid variable returned by "^caller))
       poly)

let cache_norm_sage = Ht.create 17

let _norm_sage se c hv =
  let convert_polys (p1,p2) =
    let num   = import_poly "norm_sage" p1 hv in
    let denom = import_poly "norm_sage" p2 hv in
    if e_equal denom mk_FOne then num
    else mk_FDiv num denom
  in
  try
    convert_polys (Ht.find cache_norm_sage se)
  with
    |  Not_found ->
       let cmd = YS.to_string
                  (`Assoc [ ("cmd", `String "normFieldExp")
                          ; ("varnum", `Int c)
                          ; ("fieldexp", `String (string_of_fexp se)) ])
       in
       begin match call_system Sage (cmd^"\n") 1 with
       | [ sres ] ->
         begin match YS.from_string sres with
         | `Assoc l ->
           let get k = List.assoc k l in
           begin match get "ok" with
           | `Bool true ->
             begin match get "numerator", get "denominator" with
             | `List lnum, `List ldenom -> 
               let p1 = parse_poly_json lnum in
               let p2 = parse_poly_json ldenom in
               Ht.add cache_norm_sage se (p1,p2);
               convert_polys (p1,p2)
             | _ -> failwith "error"
             end
           | _    -> failwith "error"        
           end
         | _ -> failwith "error"
         end
       | repls ->
         failwith
           (F.sprintf "norm_sage: unexpected result %s\n"
             (String.concat "\n" repls))
       end

let cache_norm_singular = Ht.create 17

let norm_singular se c hv =
  let convert_polys (p1,p2) =
    let num   = import_poly "norm_singular" p1 hv in
    let denom = import_poly "norm_singular" p2 hv in
    if e_equal denom mk_FOne then num
    else mk_FDiv num denom
  in
  try
    convert_polys (Ht.find cache_norm_singular se)
  with
    Not_found ->
    let vars = Array.to_list (Array.init c (F.sprintf "x%i")) in
    let var_string = String.concat "," (if vars = [] then ["x1"] else vars) in
    let cmd = F.sprintf "ring R = (0,%s),(a__________),dp;\n\
                         number n = %s;\nnumerator(n);denominator(n);\n"
                        var_string
                        (string_of_fexp se)
    in
    match call_system Singular cmd 3 with
    | [ _; snum; sdenom ] -> (* ring redeclared is first reply *)
      let p1 = parse_poly snum in
      let p2 = parse_poly sdenom in
      Ht.add cache_norm_singular se (p1,p2);
      convert_polys (p1,p2)
    | repls ->
      failwith (F.sprintf "norm_singular: unexpected result %s\n"
                  (String.concat "\n" repls))

let _norm_macaulay se c hv =
  let vars = Array.to_list (Array.init c (F.sprintf "x%i")) in
  let var_string = String.concat "," (if vars = [] then ["x1"] else vars) in
  let cmd = F.sprintf ("R = QQ[%s];"^^
                       "use frac R;"^^
                       "a = %s;\n"^^
                       "<< toExternalString (numerator(a)) << \"\\n\";\n"^^
                       "<< toExternalString (denominator(a)) << \"\\n\";\n")
                      var_string
                      (string_of_fexp se)
  in
  match call_system Macaulay cmd 5 with
  | [ _; _; snum; _; sdenom ] ->
      let num   = import_poly "norm_macaulay" (parse_poly snum) hv in
      let denom = import_poly "norm_macaulay" (parse_poly sdenom) hv in
      if e_equal denom mk_FOne then num
      else mk_FDiv num denom
  | repls ->
      failwith (F.sprintf "norm_macaulay: unexpected result %s\n"
                  (String.concat "\n" repls))

let cache_mod_reduce_macaulay = Ht.create 17

let _mod_reduce_macaulay a b =
  let (sa,sb,c) =
    match abstract_non_field_multiple (fun x -> x) [a;b] with
    | ([sa; sb],c,_) -> (sa,sb,c)
    | _ -> assert false
  in
  try
    Ht.find cache_mod_reduce_macaulay (sa,sb)
  with
    Not_found -> 
    let vars = Array.to_list (Array.init c (F.sprintf "x%i")) in
    let var_string = String.concat "," (if vars = [] then ["x1"] else vars) in
    let cmd = F.sprintf ("R = QQ[%s];"^^
                         "<< toExternalString((%s %% ideal(%s)) == 0) << \"\\n\";\n")
                        var_string
                        (string_of_fexp sa)
                        (string_of_fexp sb)
    in
    match call_system Macaulay cmd 2 with
    | [ _s1; sremainder ] ->
      (*i F.printf "mod_reduce %a %% %a = %s\n\n%!" pp_exp a pp_exp b sremainder; i*)
      let res = sremainder = "true" in
      Ht.add cache_mod_reduce_macaulay (sa,sb) res;
      res
    | repls ->
      failwith (F.sprintf "norm_macaulay: unexpected result %s\n"
                 (String.concat "\n" repls))

let ht_mod_reduce_singular = Ht.create 17

let mod_reduce_singular a b =
  let (sa,sb,c) =
    match abstract_non_field_multiple (fun x -> x) [a;b] with
    | ([sa; sb],c,_) -> (sa,sb,c)
    | _ -> assert false
  in
  try
    Ht.find ht_mod_reduce_singular (sa,sb)
  with
    Not_found -> 
    let vars = Array.to_list (Array.init c (F.sprintf "x%i")) in
    let var_string = String.concat "," (if vars = [] then ["x1"] else vars) in
    let cmd = F.sprintf ("ring R = (0),(%s),dp;\n"^^
                         "poly f = %s;\n ideal I = %s;\n (reduce(f,I) == 0);\n")
                        var_string
                        (string_of_fexp sa)
                        (string_of_fexp sb)
    in
    match call_system Singular cmd 2 with
    | [ _s1; sremainder ] ->
      (*i F.printf "mod_reduce %a %% %a = %s\n\n%!" pp_exp a pp_exp b sremainder; i*)
      let res = sremainder = "1" in
      Ht.add ht_mod_reduce_singular (sa,sb) res;
      res
    | repls ->
      failwith (F.sprintf "mod_reduce_singular: unexpected result %s\n"
                 (String.concat "\n" repls))

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Computing the normal form and reducing modulo a polynomial} *)

let mod_reduce = mod_reduce_singular

let norm before e =
  let (se,c,hv) = abstract_non_field before e in
  (* handle some simple special cases
     without calling Singular *)
  match se with
  | SV i                  -> Ht.find hv i
  | SNat n                -> mk_FNat n
  | SOpp(SNat n)          -> mk_FOpp (mk_FNat n)
  | SOpp(SV i)            -> mk_FOpp (Ht.find hv i)
  | SMult(SNat 1, SV i)
  | SMult(SV i, SNat 1)   -> Ht.find hv i
  | SMult(SNat i, SNat j) -> mk_FNat (i * j)
  | SMult(SV i, SV j)     -> mk_FMult (List.sort e_compare [Ht.find hv i; Ht.find hv j])
  | _                     -> norm_singular se c hv

  (*i seems like Sage is not creating the normal forms that we expect i*)
  (*i | _                     -> norm_sage se c hv i*)

(*i FIXME: add exit handlers for other systems i*)
let () =
  let exit_cmd = YS.to_string (`Assoc [ ("cmd", `String "exit") ])^"\n" in
  at_exit (fun () -> if is_started Sage then ignore (call_system Sage exit_cmd 1))

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Deducibility for fields using Sage} *)

let parse_field_json ctxs t0 =
  let rec go t =
    match t with
    | `List (`String "var"::[`Int v])  -> List.nth ctxs v
    | `List (`String "int"::[`Int i])  -> if i < 0 then mk_FOpp (mk_FNat (-i)) else mk_FNat i
    | `List (`String "+"::[`List ts])  -> mk_FPlus (List.map go ts)
    | `List [`String "/"; n; d]        -> mk_FMult [ go n; mk_FInv (go d) ]
    | `List (`String "*"::[`List ts])  -> mk_FMult (List.map go ts)
    | `List [`String "^"; t; `Int i] when i > 0 -> mk_FMult (Util.replicate i (go t))
    | _                                -> failwith (F.sprintf "parse_field_json: error %s" (YS.pretty_to_string t))
  in go t0

let _solve_fq_sage ecs e =
  let (se,secs,c) =
    match abstract_non_field_multiple (fun x -> x) (e::(List.map snd ecs)) with
    | (se::secs,c,_) -> (se,secs,c)
    | _ -> assert false
  in
  let ctxs = List.map fst ecs in
  let cmd = YS.to_string
    (`Assoc [ ("cmd", `String "solveFq")
            ; ("varnum", `Int c)
            ; ("known", `List (List.map (fun fe -> `String (string_of_fexp fe)) secs))
            ; ("secret", `String (string_of_fexp se)) ])
  in
  match call_system Sage (cmd^"\n") 1 with
  | [ sres ] ->
     begin match YS.from_string sres with
     | `Assoc l ->
       let get k = List.assoc k l in
        begin match get "ok" with
        | `Bool true  -> parse_field_json ctxs (get "res")
        | `Bool false -> raise Not_found
        | _           -> failwith "error"
        end
     | _ -> failwith "error"
     end
   | repls ->
         failwith
           (F.sprintf "norm_sage: unexpected result %s\n"
             (String.concat "\n" repls))
