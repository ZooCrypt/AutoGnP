(*s This module implements hashconsed and non-hashconsed expressions. *)

(*i*)
open Type
open Util
open Syms
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Expression data types} *)

type proj_type = ty * ty * ty

(* \ic{Constants.} *)
type cnst =
    GGen        (*r generator of $\group$ (type defines group) *)
  | FNat of int (*r Natural number in field, always $\geq 0$ *)
  | Z           (*r $0$ bitstring (typ defines length) *)
  | B of bool   (*r boolean value *)

(* \ic{Hash constants.} *)
let cnst_hash = (*c ... *) (*i*)
  function
  | GGen   -> 1
  | FNat n -> Hashcons.combine 2 n
  | Z      -> 3
  | B b    -> if b then 5 else 6
(*i*)


(* \ic{Operators with fixed arity.} *)
type op =
    GExp of Groupvar.id  (*r exponentiation in $\group_i$ *)
  | GLog of Groupvar.id  (*r discrete logarithm in $\group_i$ *)
  | FOpp                 (*r additive inverse in $\field$ *)
  | FMinus               (*r subtraction in $\field$ *)
  | FInv                 (*r mult. inverse in $\field$ *)
  | FDiv                 (*r division in $\field$ *)
  | Eq                   (*r equality *)
  | Not                  (*r negation *)
  | Ifte                 (*r if then else *)
  | EMap of Esym.t       (*r bilinear map *)


(* \ic{Hash operators.} *)
let op_hash = (*c ... *) (*i*)
  function
  | GExp gv  -> Hashcons.combine 1 (Groupvar.hash gv)
  | GLog gv  -> Hashcons.combine 2 (Groupvar.hash gv)
  | FOpp     -> 3
  | FMinus   -> 4
  | FInv     -> 5
  | FDiv     -> 6
  | Eq       -> 7
  | Not      -> 8
  | Ifte     -> 9
  | EMap(es) ->  Hashcons.combine 10 (Esym.hash es)
  (*i*)


(* \ic{N-ary/associative operators with variable arity.} *)
type nop =
    FPlus  (*r plus in Fq *)
  | FMult  (*r multiplication in Fq *)
  | Xor    (*r Xor of bitstrings *)
  | Land   (*r logical and *)
  | GMult  (*r multiplication in G (type defines group) *)

(* \ic{Hash n-ary operators.} *)
let nop_hash = (*c ... *) (*i*)
  function
  | FPlus  -> 1
  | FMult  -> 2
  | Xor    -> 3
  | Land   -> 4
  | GMult  -> 5
(*i*)


(* \ic{Expressions and expression nodes.} *)
type expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_tag  : int
}
and expr_node =
  | V      of Vsym.t          (*r variables (program, logical, random, ...) *)
  | H      of Hsym.t * expr   (*r hash function application *)
  | Tuple  of expr list       (*r tuples *)
  | Proj   of int * expr      (*r projection *)
  | Cnst   of cnst            (*r constants *)
  | App    of op * expr list  (*r fixed arity operators *)
  | Nary   of nop * expr list (*r variable arity AC operators *)
  | Exists of expr * expr * (Vsym.t * Hsym.t) list
    (*r $Exists(e_1,e_2,[(x_1,L_{H_{h1}}),\ldots]$: $\exists x_1 \in L_{H_{h1}}.\, e_1 = e_2$ *)


(* \ic{Equality hashing, and comparison for expressions.} *)
let e_equal : expr -> expr -> bool = (==) 
let e_hash e = e.e_tag
let e_compare e1 e2 = e1.e_tag - e2.e_tag 

(* \ic{Hashcons expressions.} *)
module Hse = Hashcons.Make (struct
  type t = expr

  let equal e1 e2 = (*c ... *) (*i*)
    ty_equal e1.e_ty e2.e_ty &&
    match e1.e_node, e2.e_node with
    | V v1, V v2                 -> Vsym.equal v1 v2
    | H(f1,e1), H(f2,e2)         -> Hsym.equal f1 f2 && e_equal e1 e2
    | Tuple es1, Tuple es2       -> list_eq_for_all2 e_equal es1 es2
    | Proj(i1,e1), Proj(i2,e2)   -> i1 = i2 && e_equal e1 e2
    | Cnst c1, Cnst c2           -> c1 = c2
    | App(o1,es1), App(o2,es2)   -> o1 = o2 && list_eq_for_all2 e_equal es1 es2
    | Nary(o1,es1), Nary(o2,es2) -> o1 = o2 && list_eq_for_all2 e_equal es1 es2
    | Exists(e1,e1',vh1), Exists(e2,e2',vh2) -> 
      e_equal e1 e2 && e_equal e1' e2' &&
        list_eq_for_all2 (fun (v1,h1) (v2,h2) ->
          Vsym.equal v1 v2 && Hsym.equal h1 h2) vh1 vh2
    | _, _                       -> false
  (*i*)

  let hash_node = (*c ... *) (*i*)
    function
    | V(v)       -> Vsym.hash v
    | H(f,e)     -> Hashcons.combine (Hsym.hash f) (e_hash e)
    | Tuple(es)  -> Hashcons.combine_list e_hash 3 es
    | Proj(i,e)  -> Hashcons.combine i (e_hash e)
    | Cnst(c)    -> cnst_hash c
    | App(o,es)  -> Hashcons.combine_list e_hash (op_hash o) es
    | Nary(o,es) -> Hashcons.combine_list e_hash (nop_hash o) es
    | Exists(e1,e2,vh) -> 
        Hashcons.combine_list 
          (fun (v,h) -> Hashcons.combine (Vsym.hash v) (Hsym.hash h))
          (Hashcons.combine (e_hash e1) (e_hash e2)) vh
  (*i*)

  let hash e = Hashcons.combine (ty_hash e.e_ty) (hash_node e.e_node)

  let tag n e = { e with e_tag = n }
end)

(* \ic{Create internal expression.} *)
let mk_e n ty = Hse.hashcons {
  e_node = n;
  e_ty   = ty;
  e_tag  = (-1)
}

(* \ic{Create Map, Set, and HashTable modules.} *)
module E = StructMake (struct
  type t = expr
  let tag = e_hash
end)
module Me = E.M
module Se = E.S
module He = E.H

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Indicator functions} *)

let is_V e = match e.e_node with V _ -> true | _ -> false

let is_H e = match e.e_node with H _ -> true | _ -> false

let is_Tuple e = match e.e_node with Tuple _ -> true | _ ->  false

let is_Proj e = match e.e_node with Proj _ -> true | _ ->  false

let is_some_Cnst e = match e.e_node with Cnst _ -> true | _ -> false

let is_FNat e = match e.e_node with Cnst (FNat _) -> true | _ -> false

let is_FOne e = match e.e_node with Cnst (FNat 1) -> true | _ -> false

let is_FZ e = match e.e_node with Cnst (FNat 0) -> true | _ -> false

let is_Cnst c e = match e.e_node with Cnst c' -> c = c' | _ -> false

let is_True e = is_Cnst (B true) e

let is_False e = is_Cnst (B false) e

let is_GGen e = is_Cnst GGen e

let is_some_App e = match e.e_node with App _ -> true | _ -> false

let is_App o e = match e.e_node with App(o',_) -> o = o' | _ -> false

let is_FDiv e = is_App FDiv e

let is_FOpp e = is_App FOpp e

let is_some_Nary e = match e.e_node with Nary _ -> true | _ -> false

let is_Nary o e = match e.e_node with Nary(o',_) -> o' = o | _ -> false

let is_FPlus e = is_Nary FPlus e

let is_FMult e = is_Nary FMult e

let is_Xor e = is_Nary Xor e

let is_Land e = is_Nary Land e

let is_Exists e = match e.e_node with Exists _ -> true | _ -> false

let is_GLog e = match e.e_node with App(GLog _, _) -> true | _ -> false

let is_Eq e = is_App Eq e

let is_Not e = is_App Not e

let is_field_op = function
  | FOpp | FMinus | FInv | FDiv -> true
  | GExp _ | GLog _ | EMap _
  | Eq | Ifte | Not -> false 

let is_field_nop = function
  | FPlus | FMult -> true
  | Xor | Land | GMult -> false

let is_field_exp e = match e.e_node with
  | Cnst(FNat _) -> true
  | App(o,_)     -> is_field_op o
  | Nary(o,_)    -> is_field_nop o
  | _            -> false

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Pretty printing} *)

(* \ic{The term $*(+(a,b),c)$ can be printed as $(a + b) * c$
    or $a + b * c$.
    We pass enough information to the function call
    printing $a + b$ to decide if parentheses are
    required around this expression or not.}
*)

(* \ic{Pretty print constant.} *)
let pp_cnst fmt c ty =
  match c with
  | GGen   -> if Groupvar.name (destr_G ty) <> ""
              then F.fprintf fmt "g_%a" Groupvar.pp (destr_G ty)
              else F.fprintf fmt "g"
  | FNat n -> F.fprintf fmt "%i" n
  | Z      -> F.fprintf fmt "0%%%a" pp_ty ty
  | B b    -> F.fprintf fmt "%b" b

(* \ic{Constructor above the current expression.} *)
type 'a above =
    PrefixApp          (*r prefix function application: $f(\ldots)$ *)
  | Top                (*r topmost, nothing above *)
  | Infix  of op * int (*r infix operator, i-th argument *)
  | NInfix of nop      (*r n-ary infix operator *)
  | Tup                (*r tuple constructor *)

(* \ic{Above does not have separators that allow to leave out parentheses.} *)
let notsep above = above <> Top && above <> PrefixApp && above <> Tup

(* \ic{Surround with an [hv] or [hov] box.} *)
let pp_box hv pp fmt =
  if hv
  then F.fprintf fmt "@[<hv>%a@]" pp
  else F.fprintf fmt "@[<hov>%a@]" pp

(* \ic{Enclose with given format strings.} *)
let pp_enclose hv ~pre ~post pp fmt x =
  F.fprintf fmt "%(%)%a%(%)" pre (pp_box hv pp) x post

(* \ic{Enclose with parens.} *)
let pp_paren hv = pp_enclose hv ~pre:"(" ~post:")"

(* \ic{Enclose with parens depending on boolean argument.} *)
let pp_maybe_paren hv c = pp_if c (pp_paren hv) (pp_box hv)

(* \ic{Pretty-prints expression assuming that
       the expression above is of given type.} *)
let rec pp_exp_p above fmt e =
  match e.e_node with
  | V(v)       -> 
    (* F.fprintf fmt "%a.%i" Vsym.pp v (Vsym.hash v) *)
    F.fprintf fmt "%a" Vsym.pp v
  | H(h,e)     -> 
    F.fprintf fmt "@[<hov>%a(%a)@]" Hsym.pp h (pp_exp_p PrefixApp) e
  | Tuple(es)  -> 
    let pp fmt = 
      F.fprintf fmt "@[<hov>%a@]" (pp_list ",@," (pp_exp_p Tup)) in
    pp_maybe_paren false (above <> PrefixApp) pp fmt es
  | Proj(i,e)  -> 
    F.fprintf fmt "%a%s%i" (pp_exp_p PrefixApp) e "\\" i
  | Cnst(c)    -> pp_cnst fmt c e.e_ty
  | App(o,es)  -> pp_op_p above fmt (o,es) 
  | Nary(o,es) -> pp_nop_p above fmt (o,es)
  | Exists(e1,e2,h) ->
    let pp fmt () = 
      F.fprintf fmt "@[<hv 2>exists %a:@ %a =@ %a@]"
        (pp_list ",@ " (fun fmt (v,h) ->
          F.fprintf fmt "%a <- L_%a" Vsym.pp v Hsym.pp h)) h 
        (pp_exp_p Top) e1 (pp_exp_p Top) e2 in
    pp_maybe_paren true (notsep above && above<>NInfix(Land)) pp fmt ()

(* \ic{Pretty-prints operator assuming that
       the expression above is of given type.} *)
and pp_op_p above fmt (op, es) =
  let pp_bin p op ops a b =
    let pp fmt () = 
      F.fprintf fmt "@[<hv>%a@ %s %a@]"
        (pp_exp_p (Infix(op,0))) a ops
        (pp_exp_p (Infix(op,1))) b in
    pp_maybe_paren true p pp fmt ()
  in
  let pp_prefix op before after a =
    F.fprintf fmt "%s%a%s" before (pp_exp_p (Infix(op,0))) a after
  in
  match op, es with
  | GExp _,   [a;b] -> 
    pp_bin (notsep above && above<>NInfix(GMult) && above<>NInfix(GMult))
      op "^" a b
  | FDiv,   [a;b] -> 
    pp_bin (notsep above) FDiv "/" a b
  | FMinus, [a;b] -> 
    pp_bin (notsep above && above<>Infix(FMinus,0)) FMinus "-" a b
  | Eq,     [a;b] -> 
    pp_bin (notsep above && above<>NInfix(Land)) Eq "=" a b
  | GLog _, [a]   ->
    F.fprintf fmt "@[<hov>log(%a)@]" (pp_exp_p PrefixApp) a
  | FOpp,   [a]   ->
    pp_prefix FOpp  "-"     ""    a
  | FInv,   [a]   -> 
    pp_prefix FInv  ""      "^-1" a
  | Not,    [a]   -> 
    pp_prefix Not   "not "  ""    a
  | EMap es,[a;b] ->
    let ppe i = pp_exp_p (Infix(EMap es,i)) in
    F.fprintf fmt "e(%a,%a)" (ppe 0) a (ppe 1) b
  | Ifte, [a;b;d] ->
    let ppe i = pp_exp_p (Infix(Ifte,i)) in
    let pp fmt () = 
      F.fprintf fmt "@[<hv>%a?%a:%a@]" (ppe 0) a (ppe 1) b (ppe 2) d
    in
    pp_maybe_paren true (notsep above) pp fmt ()
  | _             -> failwith "pp_op: invalid expression"

(* \ic{Pretty-prints n-ary operator assuming that
       the expression above is of given type.} *)
and pp_nop_p above fmt (op,es) =
  let pp_nary hv op ops p =
    pp_maybe_paren hv p (pp_list ops (pp_exp_p (NInfix(op)))) fmt es in
  match op with
  | GMult  -> pp_nary true GMult  "@ * "   (notsep above)
  | FPlus  -> pp_nary true FPlus  "@ + "   (notsep above)
  | Xor    -> pp_nary true Xor    "@ ++ " (notsep above)
  | Land   -> pp_nary true Land   "@ /\\ " (notsep above)
  | FMult  ->
    let p = 
      match above with
      | NInfix(FPlus) | Infix(FMinus,_) -> false
      | _ -> notsep above in
    pp_nary false FMult "@,*" p

(* \ic{Pretty-print expressions/operators assuming they are topmost.} *)
let pp_exp fmt e = pp_exp_p Top fmt e
let pp_op  fmt x = pp_op_p  Top fmt x
let pp_nop fmt x = pp_nop_p Top fmt x

(* \ic{Pretty-printing without parens around tuples.} *)
let pp_exp_tnp fmt e = pp_exp_p PrefixApp fmt e

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Destructor functions} *)

exception Destr_failure of string

let destr_V e = match e.e_node with V v -> v | _ -> raise (Destr_failure "V")

let destr_H e = 
  match e.e_node with H(h,e) -> (h,e) | _ -> raise (Destr_failure "H")

let destr_Tuple e = 
  match e.e_node with Tuple(es) -> (es) | _ -> raise (Destr_failure "Tuple")

let destr_Proj e = 
  match e.e_node with Proj(i,e) -> (i,e) | _ -> raise (Destr_failure "Proj")

let destr_Cnst e = 
  match e.e_node with Cnst(c) -> (c) | _ -> raise (Destr_failure "Cnst")

let destr_FNat e =
  match e.e_node with
  | Cnst (FNat n) -> n
  | _ -> raise (Destr_failure "FNat")

let destr_App e =
  match e.e_node with App(o,es) -> (o,es) | _ -> raise (Destr_failure "App")

let destr_App_uop s o e = 
  match e.e_node with 
  | App(o',[e1]) when o = o' -> e1
  | _ -> raise (Destr_failure s)
  
let destr_App_bop s o e =
  match e.e_node with 
  | App(o',[e1;e2]) when o = o' -> (e1,e2)
  | _ -> raise (Destr_failure s)

let destr_Nary s o e =
  match e.e_node with
  | Nary(o',es) when o = o' -> es 
  | _ -> raise (Destr_failure s)

let destr_GMult  e = destr_Nary "GMult"  GMult e

let destr_GExp   e = 
  match e.e_node with 
  | App(GExp _,[e1;e2]) -> e1,e2
  | _ -> raise (Destr_failure "GExpr")

let destr_GLog   e =
  match e.e_node with 
  | App(GLog _,[e1]) -> e1
  | _ -> raise (Destr_failure "GLog")

let destr_EMap   e =
  match e.e_node with 
  | App(EMap es,[e1;e2]) -> es,e1,e2
  | _ -> raise (Destr_failure (fsprintf "EMap for %a" pp_exp e))

let destr_FOpp   e = destr_App_uop "FOpp"   FOpp e
let destr_FMinus e = destr_App_bop "FMinus" FMinus e
let destr_FInv   e = destr_App_uop "FInv"   FInv e
let destr_FDiv   e = destr_App_bop "FDiv"   FDiv e 
let destr_FPlus  e = destr_Nary   "FPlus"  FPlus e
let destr_FMult  e = destr_Nary   "FMult"  FMult e

let destr_Eq     e = destr_App_bop "Eq"   Eq e 
let destr_Not    e = destr_App_uop "Not"  Not e
let destr_Xor    e = destr_Nary   "Xor"  Xor e 
let destr_Land   e = destr_Nary   "Land" Land e

let destruct_Lxor e = 
  match e.e_node with
  | Nary(Xor,es) -> es 
  | _ -> [e] 

let destruct_Land e =
  match e.e_node with
  | Nary(Land,es) -> es 
  | _ -> [e] 

let destr_Ifte   e = 
  match e.e_node with 
  | App(Eq,[a;b;c]) -> (a,b,c) 
  | _ -> raise (Destr_failure "Ifte")
let destr_Exists  e = 
  match e.e_node with
  | Exists(e1,e2,vh) -> e1,e2,vh
  | _ -> raise (Destr_failure "Exists")

(*i ----------------------------------------------------------------------- i*)
(*  \subsection{Constructor functions} *)

exception TypeError of (ty * ty * expr * expr option * string)

let ensure_ty_equal ty1 ty2 e1 e2 s =
  ignore (ty_equal ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

let ensure_ty_G ty s =
  match ty.ty_node with
  | G gv -> gv
  | _    ->
    failwith (fsprintf "%s: expected group type, got %a" s pp_ty ty)

let ty_G gv = mk_ty (G gv)
let ty_Fq = mk_ty Fq
let ty_Bool = mk_ty Bool
let ty_BS lv = mk_ty (BS lv)
let ty_Prod tys = mk_ty (Prod tys)

let mk_V v = mk_e (V v) v.Vsym.ty
  
let mk_H h e =
  ensure_ty_equal e.e_ty h.Hsym.dom e None "mk_H";
  mk_e (H(h,e)) h.Hsym.codom

let mk_Tuple es =
  mk_e (Tuple es) (ty_Prod (L.map (fun e -> e.e_ty) es))

let mk_Proj i e = 
  match e.e_ty.ty_node with
  | Prod(tys) when i >= 0 && L.length tys > i -> 
    mk_e (Proj(i,e)) (L.nth tys i)
  | _ ->
    let s =
      F.sprintf
        "mk_Proj expects product type with at least %i components"
        (i+1)
    in
    raise (TypeError(e.e_ty,e.e_ty,e,None,s))

let mk_Exists e1 e2 h =
  ensure_ty_equal e1.e_ty e2.e_ty e1 None "mk_ElemH";
  L.iter (fun (v,h) ->
    ensure_ty_equal v.Vsym.ty h.Hsym.dom (mk_V v) None "mk_ElemH") h;
  mk_e (Exists(e1,e2,h)) ty_Bool
  
let mk_Cnst c ty = mk_e (Cnst c) ty

let mk_GGen gv = mk_Cnst GGen (ty_G gv)
let mk_FNat n = assert (n >= 0); mk_Cnst (FNat n) ty_Fq
let mk_FOne = mk_Cnst (FNat 1) ty_Fq
let mk_FZ = mk_Cnst (FNat 0) ty_Fq
let mk_Z lv = mk_Cnst Z (ty_BS lv)
let mk_B  b = mk_Cnst (B b) ty_Bool
let mk_True = mk_B true
let mk_False = mk_B false


let mk_App o es ty = mk_e (App(o,es)) ty

let mk_GExp a b =
  let gv = ensure_ty_G a.e_ty "mk_GExp" in
  ensure_ty_equal b.e_ty ty_Fq b None "mk_GExp";
  mk_App (GExp gv) [a;b] a.e_ty

let mk_GLog a =
  let gv = ensure_ty_G a.e_ty "mk_GLog" in
  mk_App (GLog gv) [a] ty_Fq

let mk_EMap es a b =
  ensure_ty_equal a.e_ty (ty_G es.Esym.source1) a None "mk_EMap";
  ensure_ty_equal b.e_ty (ty_G es.Esym.source2) b None "mk_EMap";
  mk_App (EMap es) [a;b] (ty_G es.Esym.target)

let mk_FOpp a =
  ensure_ty_equal a.e_ty ty_Fq a None "mk_FOpp";
  mk_App FOpp [a] ty_Fq

let mk_FMinus a b =
  ensure_ty_equal a.e_ty ty_Fq a None "mk_FMinus";
  ensure_ty_equal b.e_ty ty_Fq b None "mk_FMinus";
  mk_App FMinus [a;b] ty_Fq

  let mk_FInv a =
    ensure_ty_equal a.e_ty ty_Fq a None "mk_FInv";
    mk_App FInv [a] ty_Fq

let mk_FDiv a b =
  ensure_ty_equal a.e_ty ty_Fq a None "mk_FDiv";
  ensure_ty_equal b.e_ty ty_Fq b None "mk_FDiv";
  mk_App FDiv [a;b] ty_Fq

let mk_Eq a b =
  ensure_ty_equal a.e_ty b.e_ty a (Some b) "mk_Eq";
  mk_App Eq [a;b] ty_Bool

let mk_Not a =
  ensure_ty_equal a.e_ty ty_Bool a None "mk_Not";
  mk_App Not [a] ty_Bool

let mk_Ifte a b c =
  ensure_ty_equal a.e_ty ty_Bool a None "mk_Ifte";
  ensure_ty_equal b.e_ty c.e_ty b (Some c) "mk_Ifte";
  mk_App Ifte [a;b;c] b.e_ty


let rec flatten nop es =
  let go e = match e.e_node with
    | Nary(nop1, es1) when nop1 = nop ->
      flatten nop es1
    | _ -> [ e ]
  in
  L.concat (L.map go es)

let mk_nary s sort o es ty =
  let es = flatten o es in
  let es = if sort then L.sort e_compare es else es in
  match es with
  | []  -> failwith (F.sprintf "%s: empty list given" s);
  | [a] -> a
  | _   ->
    L.iter (fun e -> ensure_ty_equal e.e_ty ty e None s) es;
    mk_e (Nary(o,es)) ty

let mk_FPlus es = mk_nary "mk_FPlus" true FPlus es ty_Fq 

let mk_FMult es = mk_nary "mk_FMult" true FMult es ty_Fq

let mk_Xor es =
  match es with
  | e::_ ->
    begin match e.e_ty.ty_node with
    | BS _ | Bool -> mk_nary "mk_Xor" true Xor es e.e_ty
    | _ -> failwith "mk_Xor: expected bitstring argument"
    end
  | _ -> failwith "mk_Xor: expected non-empty list"

let mk_Land es = mk_nary "mk_Land" false Land es ty_Bool

let mk_GMult es =
  match es with
  | e::_ ->
    begin match e.e_ty.ty_node with
    | G gv -> mk_nary "mk_GMult" true GMult es (ty_G gv)
    | _ -> assert false
    end
  | _ -> assert false

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Generic functions on expressions} *)

let sub_map g e = 
  match e.e_node with
  | V _ | Cnst _ -> e
  | H(h,e1) ->
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (H(h,e1')) e.e_ty
  | Exists(e1,e2,h) ->
      let e1' = g e1 in
      let e2' = g e2 in
      if e1 == e1' && e2 == e2' then e
      else mk_e (Exists(e1',e2',h)) e.e_ty
  | Tuple(es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (Tuple(es')) e.e_ty
  | Proj(i, e1) ->
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (Proj(i,e1')) e.e_ty
  | App(o, es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (App(o,es')) e.e_ty
  | Nary(o, es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (Nary(o,es')) e.e_ty

let check_fun g e =
  let e' = g e in 
  ensure_ty_equal e'.e_ty e.e_ty e (Some e') "check_fun";
  e'

let e_sub_map g = sub_map (check_fun g)

let e_sub_fold g acc e =
  match e.e_node with
  | V _ | Cnst _ -> acc
  | H(_,e) | Proj(_, e) -> g acc e
  | Exists(e1,e2,_) -> g (g acc e1) e2
  | Tuple(es) | App(_, es) | Nary(_, es)-> L.fold_left g acc es

let e_sub_iter g e = 
  match e.e_node with
  | V _ | Cnst _ -> ()
  | H(_,e) | Proj(_, e) -> g e
  | Exists(e1,e2,_) -> g e1; g e2
  | Tuple(es) | App(_, es) | Nary(_, es)-> L.iter g es

let rec e_iter g e =
  g e; e_sub_iter (e_iter g) e

let e_sub_exists f =
  e_sub_fold (fun acc e -> acc || f e) false

let rec e_exists f e =
  f e || e_sub_exists (e_exists f) e

let e_sub_forall f =
  e_sub_fold (fun acc e -> acc && f e) true

let rec e_forall f e = 
  f e && e_sub_forall (e_forall f) e

let e_find f (e : expr) = 
  let module E = struct exception Found of expr end in
  let rec aux e = 
    if f e then raise (E.Found e)
    else e_sub_iter aux e in
  try aux e; raise Not_found with E.Found e -> e

let e_find_all f e =
  let rec aux s e =
    let s = if f e then Se.add e s else s in
    e_sub_fold aux s e in
  aux Se.empty e

let e_vars = e_find_all is_V

let e_ty_outermost ty e =
  let res = ref [] in
  let rec go e =
    if Type.ty_equal e.e_ty ty && not (L.mem e !res) then
      res := e::!res
    else
      e_sub_iter go e
  in
  go e;
  L.rev !res

let has_log e = e_exists (fun e -> is_GLog e) e

(*i FIXME: is this sufficient? i*)
let is_ppt e = not (has_log e)

let e_map f = 
  let tbl = He.create 103 in
  let rec aux e = 
    try He.find tbl e 
    with _ ->
      let e' = f (sub_map aux e) in
      ensure_ty_equal e'.e_ty e.e_ty e (Some e') "e_rec_map";
      He.add tbl e e';
      e' in
  aux

let e_map_ty_maximal ty g e0 = 
  let rec go ie e =
    (* me = e is a maximal expression of the desired type *)
    let me = not ie && ty_equal e.e_ty ty in
    (* ie = immediate subterms of e are inside a larger expression of the desired type *)
    let ie = me || (ie && ty_equal e.e_ty ty) in
    let trans = if me then g else id in
    match e.e_node with
    | V(_) | Cnst(_) -> e
    | H(f,e) ->
      let e = go ie e in
      trans (mk_H f e)
    | Tuple(es) ->
      let es = L.map (go ie) es in
      trans (mk_Tuple es)
    | Proj(i,e) ->
      let e = go ie e in
      trans (mk_Proj i (go ie e))
    | App(o,es) ->
      let es = L.map (go ie) es in
      trans (mk_App o es e.e_ty) 
    | Nary(o,es) -> 
      let es = L.map (go ie) es in
      trans (mk_e (Nary(o,es)) e.e_ty)
    | Exists(e1,e2,vh) ->
      let (e1, e2) = (go ie e1, go ie e2) in
      trans (mk_Exists e1 e2 vh)
  in
  go false e0

let e_iter_ty_maximal ty g e0 = 
  let rec go ie e0 =
    (* me = e is a maximal expression of the desired type *)
    let me = not ie && ty_equal e0.e_ty ty in
    (* ie = immediate subterms of e inside a larger expression of the desired type *)
    let ie = me || (ie && ty_equal e0.e_ty ty) in
    (* F.printf "### %a ie=%b me=%b\n\n" pp_exp e0 ie me; *)
    let run = if me then g else fun _ -> () in
    match e0.e_node with
    | V(_) | Cnst(_) -> ()
    | H(_,e) ->
      go ie e;
      run e0
    | Tuple(es) ->
      L.iter (go ie) es;
      run e0
    | Proj(_,e) ->
      go ie e;
      run e0
    | App(_,es) ->
      L.iter (go ie) es;
      run e0
    | Nary(_,es) -> 
      L.iter (go ie) es;
      run e0
    | Exists(e1,e2,_) ->
      go ie e1; go ie e2;
      run e0
  in
  go false e0


let e_map_top f = 
  let tbl = He.create 103 in
  let rec aux e = 
    try He.find tbl e 
    with Not_found ->
      let e' = try check_fun f e with Not_found -> sub_map aux e in
      He.add tbl e e';
      e'
  in
  aux 

let e_replace e1 e2 = 
  e_map_top (fun e -> if e_equal e e1 then e2 else raise Not_found)

let e_subst s = e_map_top (fun e -> Me.find e s)

let se_of_list = L.fold_left (fun s e -> Se.add e s) Se.empty

type ctxt = Vsym.t * expr

let inst_ctxt (v, e') e = e_replace (mk_V v) e e'

let typeError_to_string (ty1,ty2,e1,me2,s) =
  match me2 with
  | Some e2 -> 
    fsprintf
      "incompatible types `%a' vs. `%a' for expressions `%a' and `%a' in %s"
      pp_ty ty1 pp_ty ty2 pp_exp e1 pp_exp e2 s
  | None when ty_equal ty1 ty2 ->
    fsprintf "type error in `%a' of type %a: %s" pp_exp e1 pp_ty ty1 s
  | None ->
    fsprintf
      "expected type `%a', got  `%a' for Expression `%a': %s"
      pp_ty ty1 pp_ty ty2 pp_exp e1 s

let catch_TypeError f =
  try f()
  with TypeError(ty1,ty2,e1,me2,s) ->
    print_string (typeError_to_string (ty1,ty2,e1,me2,s));
    raise (TypeError(ty1,ty2,e1,me2,s))

let sub t = 
  let rec aux e1 e2 = 
    match e2.e_ty.ty_node with
    | Bool -> mk_Xor [e1;e2], mk_False
    | BS t -> mk_Xor [e1;e2], mk_Z t
    | G  id -> 
      let g = mk_GGen id in
      mk_GExp g (mk_FMinus (mk_GLog e1) (mk_GLog e2)), mk_GExp g mk_FZ
    | Fq   -> mk_FMinus e1 e2, mk_FZ
    | Prod lt ->
      let es, zs = 
        L.split 
          (L.mapi (fun i _ -> aux (mk_Proj i e1) (mk_Proj i e2)) lt) in
      mk_Tuple es, mk_Tuple zs
    | Int -> assert false in
  let x1 =  Vsym.mk "x"  t in
  let x2 = Vsym.mk "x" t in
  let e, z = aux (mk_V x1) (mk_V x2) in
  (x1,(x2,e)), z
    
let mk_Zero t = snd (sub t)

let rec is_Zero e = 
  match e.e_node with
  | Cnst (B false)       -> true
  | Cnst (FNat 0)        -> true
  | Cnst Z               -> true
  | Tuple es             -> L.for_all is_Zero es
  | App(GExp _, [e1;e2]) -> is_Zero e2 || is_Zero e1
  | _                    -> false

type inverter = I of expr

let expr_of_inverter (I e) = e
