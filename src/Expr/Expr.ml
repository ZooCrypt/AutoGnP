open Type
open Util
open IdType

(* ----------------------------------------------------------------------- *)
(** {1 Expressions} *)

type 'a proj_type = 'a gty * 'a gty * 'a gty

(* constants *)
type cnst =
    GGen        (* generator of G (type defines group) *)
  | FNat of int (* Natural number in field, always >= 0 *)
  | Z           (* 0 bitstring (typ defines length) *)
  | B of bool   (* boolean value *)

let cnst_hash = function
  | GGen   -> 1
  | FNat n -> Hashcons.combine 2 n
  | Z      -> 3
  | B b  -> if b then 5 else 6

(* operators with fixed arity *)
type 'a gop =
    GExp of 'a Groupvar.gid  (* exponentiation in source group *)
  | GLog of 'a Groupvar.gid  (* discrete logarithm in group *)
  | FOpp                     (* additive inverse in Fq *)
  | FMinus                   (* subtraction in Fq *)
  | FInv                     (* mult. inverse in Fq *)
  | FDiv                     (* division in Fq *)
  | Eq                       (* equality *)
  | Not                      (* negation *)
  | Ifte                     (* if then else *)
  | EMap of 'a Esym.gt       (* bilinear map *)

type op = internal gop
type eop = exported gop

let op_hash = function
    GExp gv  -> Hashcons.combine 1 (Groupvar.hash gv)
  | GLog gv  -> Hashcons.combine 2 (Groupvar.hash gv)
  | FOpp     -> 3
  | FMinus   -> 4
  | FInv     -> 5
  | FDiv     -> 6
  | Eq       -> 7
  | Not      -> 8
  | Ifte     -> 9
  | EMap(es) ->  Hashcons.combine 10 (Esym.hash es)

(* associative operators with variable arity *)
type nop =
    FPlus  (* plus in Fq *)
  | FMult  (* multiplication in Fq *)
  | Xor    (* Xor of bitstrings *)
  | Land   (* logical and *)
  | GMult  (* multiplication in G (type defines group) *)

let nop_hash = function
    FPlus  -> 1
  | FMult  -> 2
  | Xor    -> 3
  | Land   -> 4
  | GMult  -> 5

type 'a gexpr = {
  e_node : 'a gexpr_node;
  e_ty   : 'a gty;
  e_tag  : int
}
and 'a gexpr_node =
  | V     of 'a Vsym.gt                 (* variables (program, logical, random, ...) *)
  | H     of 'a Hsym.gt * 'a gexpr      (* hash function application *)
  | Tuple of ('a gexpr) list            (* tuples *)
  | Proj  of int * 'a gexpr             (* projection *)
  | Cnst  of cnst                       (* constants *)
  | App   of 'a gop * 'a gexpr list     (* fixed arity operators *)
  | Nary  of nop * 'a gexpr list        (* variable arity AC operators *)
  | Exists of 'a gexpr * 'a gexpr * ('a Vsym.gt * 'a Hsym.gt) list
    (* Exists(e1,e2,[(x1,L_Hh1)...]: exists  x1 <- L_Hh1, e1 = e2 *)


type expr = internal gexpr
type expr_node = internal gexpr_node

type eexpr = exported gexpr
type eexpr_node = exported gexpr_node

let e_equal : expr -> expr -> bool = (==) 
let e_hash e = e.e_tag
let e_compare e1 e2 = e1.e_tag - e2.e_tag 

module Hse = Hashcons.Make (struct
  type t = expr

  let equal e1 e2 =
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

  let hash_node = function
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

  let hash e =
    Hashcons.combine (ty_hash e.e_ty) (hash_node e.e_node)

  let tag n e = { e with e_tag = n }
end)

let mk_e n ty = Hse.hashcons {
  e_node = n;
  e_ty   = ty;
  e_tag  = (-1)
}

let mk_ee n ty = {
  e_node = n;
  e_ty   = ty;
  e_tag  = (-1)
}

let op_export o = match o with
  | GExp gv  -> GExp(Groupvar.export gv)
  | GLog gv  -> GLog(Groupvar.export gv)
  | FOpp     -> FOpp
  | FMinus   -> FMinus
  | FInv     -> FInv
  | FDiv     -> FDiv
  | Eq       -> Eq
  | Not      -> Not
  | Ifte     -> Ifte
  | EMap(es) -> EMap(Esym.export es)

let rec e_export e =
  let ty = ty_export e.e_ty in
  let e = match e.e_node with
    | V(v)       -> V(Vsym.export v)
    | H(f,e)     -> H(Hsym.export f, e_export e)
    | Tuple(es)  -> Tuple(List.map e_export es)
    | Proj(i,e)  -> Proj(i,e_export e)
    | Cnst(c)    -> Cnst(c)
    | App(o,es)  -> App(op_export o, List.map e_export es)
    | Nary(o,es) -> Nary(o, List.map e_export es)
    | Exists(e1,e2,h) -> 
      Exists(e_export e1,e_export e2,
            List.map (fun (v,h) -> Vsym.export v, Hsym.export h) h)
  in mk_ee e ty


module E = StructMake (struct
  type t = expr
  let tag = e_hash
end)

module Me = E.M
module Se = E.S
module He = E.H

(* ----------------------------------------------------------------------- *)
(** {2 Indicator functions} *)

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

(* ----------------------------------------------------------------------- *)
(** {3 Pretty printing} *)

let pp_cnst fmt c ty =
  match c with
  | GGen   -> if Groupvar.name (destr_G ty) <> ""
              then F.fprintf fmt "g_%a" Groupvar.pp (destr_G ty)
              else F.fprintf fmt "g"
  | FNat n -> F.fprintf fmt "%i" n
  | Z      -> F.fprintf fmt "0%%%a" pp_ty ty
  | B b    -> F.fprintf fmt "%b" b

(* The term   *
             / \
            %   c
           / \
          a   b
    can be printed as 'a % b # c' or '(a % b) # c'.
    We pass enough information to the function call
    printing 'a % b' to decide if parentheses are
    required around this expression or not.
*)

type 'a above =
    PrefixApp (* prefix function application: hash, emap, ... *)
  | Top
  | Infix  of 'a gop * int (* infix operator, i-th argument *)
  | NInfix of nop (* nary infix operator *)
  | Tup

(* Generic function for printing *)
let pp_if c pp1 pp2 fmt x =
  match c with
  | true  -> pp1 fmt x
  | false -> pp2 fmt x

let pp_enclose hv ~pre ~post pp fmt x =
  if hv then
    F.fprintf fmt "%(%)@[<hv>%a@]%(%)" pre pp x post
  else
    F.fprintf fmt "%(%)@[<hov>%a@]%(%)" pre pp x post

let pp_paren hv pp fmt x =
  pp_enclose hv ~pre:"(" ~post:")" pp fmt x

let pp_box hv pp fmt =
  if hv then
    F.fprintf fmt "@[<hv>%a@]" pp
  else
    F.fprintf fmt "@[<hov>%a@]" pp

let pp_maybe_paren hv c pp =
   pp_if c (pp_paren hv) (pp_box hv) pp

(* above does not have separators that allow to leave out parentheses *)
let notsep above = above <> Top && above <> PrefixApp && above <> Tup

let rec pp_exp_p above fmt e =
  match e.e_node with
  | V(v)       -> 
    (* F.fprintf fmt "%a_%i" Vsym.pp v (Id.tag v.Vsym.id) *)
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
      F.fprintf fmt "@[<hv 2>exists %a,@ %a =@ %a@]"
        (pp_list ",@ " (fun fmt (v,h) ->
          F.fprintf fmt "%a <- L_%a" Vsym.pp v Hsym.pp h)) h 
        (pp_exp_p Top) e1 (pp_exp_p Top) e2 in
    pp_maybe_paren true (notsep above && above<>NInfix(Land)) pp fmt ()

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

let pp_exp fmt e = pp_exp_p Top fmt e
let pp_op  fmt x = pp_op_p  Top fmt x
let pp_nop fmt x = pp_nop_p Top fmt x

(* no parens around tuples *)
let pp_exp_tnp fmt e = pp_exp_p PrefixApp fmt e

(* ----------------------------------------------------------------------- *)
(** {4 Destructor functions} *)

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

(* ----------------------------------------------------------------------- *)
(** {5 Constructor functions} *)

(** We use a functor so that we don't have to duplicate code for
    hashconsed/internal expressions and external expressions. *)

module type GexprBuild = sig
  type t
  val mk : t gexpr_node -> t gty -> t gexpr
  val ty_equal : t gty -> t gty -> bool
  val comp : t gexpr -> t gexpr -> int
  val mk_ty : t gty_node -> t gty
end

module ExprBuild : GexprBuild with type t = internal = struct
  type t = internal
  let mk = mk_e
  let comp = e_compare
  let ty_equal = Type.ty_equal
  let mk_ty =  mk_ty
end

module EexprBuild : GexprBuild with type t = exported = struct
  type t = exported
  let mk = mk_ee
  let comp = compare
  let ty_equal = (=)
  let mk_ty = mk_ety
end

module type S =
sig
  type t
  exception TypeError of (t gty *  t gty * (t gexpr) * (t gexpr) option * string)
  val ensure_ty_equal : t gty -> t gty -> t gexpr -> t gexpr option -> string -> unit
  val mk_V : t Vsym.gt -> t gexpr
  val mk_H : t Hsym.gt -> t gexpr -> t gexpr
  val mk_Tuple  : (t gexpr) list -> t gexpr
  val mk_Proj   : int -> t gexpr -> t gexpr
  val mk_Exists : t gexpr -> t gexpr -> (t Vsym.gt * t Hsym.gt) list -> t gexpr
  
  val mk_GGen  : t Groupvar.gid -> t gexpr
  val mk_FNat  : int -> t gexpr
  val mk_FZ    : t gexpr
  val mk_FOne  : t gexpr
  val mk_Z     : t Lenvar.gid -> t gexpr
  val mk_B     : bool -> t gexpr
  val mk_True  : t gexpr
  val mk_False : t gexpr

  val mk_GMult : t gexpr list -> t gexpr
  val mk_GExp : t gexpr -> t gexpr -> t gexpr
  val mk_GLog : t gexpr -> t gexpr
  val mk_EMap : t Esym.gt -> t gexpr -> t gexpr -> t gexpr
  val mk_FOpp : t gexpr -> t gexpr
  val mk_FMinus : t gexpr -> t gexpr -> t gexpr
  val mk_FInv : t gexpr -> t gexpr
  val mk_FDiv : t gexpr -> t gexpr -> t gexpr
  val mk_Eq : t gexpr -> t gexpr -> t gexpr
  val mk_Not : t gexpr -> t gexpr  
  val mk_Ifte : t gexpr -> t gexpr -> t gexpr -> t gexpr

  val mk_FPlus : (t gexpr) list -> t gexpr
  val mk_FMult : (t gexpr) list -> t gexpr
  val mk_Xor : (t gexpr) list -> t gexpr
  val mk_Land : (t gexpr) list -> t gexpr
end

module Make (E : GexprBuild) : S with type t = E.t =
struct
  type t = E.t

  exception TypeError of (E.t gty * E.t gty * E.t gexpr * E.t gexpr option * string)

  let ensure_ty_equal ty1 ty2 e1 e2 s =
    ignore (E.ty_equal ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

  let ensure_ty_G ty s =
    match ty.ty_node with
    | G gv -> gv
    | _    ->
      failwith (fsprintf "%s: expected group type, got %a" s pp_ty ty)

  let ty_G gv = E.mk_ty (G gv)
  let ty_Fq = E.mk_ty Fq
  let ty_Bool = E.mk_ty Bool
  let ty_BS lv = E.mk_ty (BS lv)
  let ty_Prod tys = E.mk_ty (Prod tys)

  let mk_V v = E.mk (V v) v.Vsym.ty
  
  let mk_H h e =
    ensure_ty_equal e.e_ty h.Hsym.dom e None "mk_H";
    E.mk (H(h,e)) h.Hsym.codom

  let mk_Tuple es =
    E.mk (Tuple es) (ty_Prod (List.map (fun e -> e.e_ty) es))

  let mk_Proj i e = 
    match e.e_ty.ty_node with
    | Prod(tys) when i >= 0 && List.length tys > i -> 
      E.mk (Proj(i,e)) (List.nth tys i)
    | _ ->
      (* FIXME: the message you get from this is really confusing,
        expected t, got t, ..., expected product type *)
      raise (TypeError(e.e_ty,e.e_ty,e,None,
             (F.sprintf "mk_Proj expected product type with at least %i components" (i+1))))

  let mk_Exists e1 e2 h =
    ensure_ty_equal e1.e_ty e2.e_ty e1 None "mk_ElemH";
    List.iter (fun (v,h) ->
      ensure_ty_equal v.Vsym.ty h.Hsym.dom (mk_V v) None "mk_ElemH") h;
    E.mk (Exists(e1,e2,h)) ty_Bool
  
  let mk_Cnst c ty = E.mk (Cnst c) ty

  let mk_GGen gv = mk_Cnst GGen (ty_G gv)
  let mk_FNat n = assert (n >= 0); mk_Cnst (FNat n) ty_Fq
  let mk_FOne = mk_Cnst (FNat 1) ty_Fq
  let mk_FZ = mk_Cnst (FNat 0) ty_Fq
  let mk_Z lv = mk_Cnst Z (ty_BS lv)
  let mk_B  b = mk_Cnst (B b) ty_Bool
  let mk_True = mk_B true
  let mk_False = mk_B false


  let mk_App o es ty = E.mk (App(o,es)) ty

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
    List.concat (List.map go es)

  let mk_nary s sort o es ty =
    let es = flatten o es in
    let es = if sort then List.sort E.comp es else es in
    match es with
    | []  -> failwith (F.sprintf "%s: empty list given" s);
    | [a] -> a
    | _   -> List.iter (fun e -> ensure_ty_equal e.e_ty ty e None s) es;
             E.mk (Nary(o,es)) ty

  let mk_FPlus es = mk_nary "mk_FPlus" true FPlus es ty_Fq 
  let mk_FMult es = mk_nary "mk_FMult" true FMult es ty_Fq
  let mk_Xor es = match es with
    | e::_ -> (match e.e_ty.ty_node with
               | BS _ | Bool -> mk_nary "mk_Xor" true Xor es e.e_ty
               | _ -> failwith "mk_Xor: expected bitstring argument")
    | _ -> failwith "mk_Xor: expected non-empty list"
  let mk_Land es = mk_nary "mk_Land" false Land es ty_Bool
  let mk_GMult es =
    match es with
    | e::_ ->
        (match e.e_ty.ty_node with
         | G gv -> mk_nary "mk_GMult" true GMult es (ty_G gv)
         | _ -> assert false)
    | _ -> assert false

end

module Constructors : S with type t = internal = Make(ExprBuild) 
module EConstructors : S with type t = exported = Make(EexprBuild)

include Constructors

(* ----------------------------------------------------------------------- *)
(** {6 Generic functions on [expr]} *)

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
  | Tuple(es) | App(_, es) | Nary(_, es)-> List.fold_left g acc es

let e_sub_iter g e = 
  match e.e_node with
  | V _ | Cnst _ -> ()
  | H(_,e) | Proj(_, e) -> g e
  | Exists(e1,e2,_) -> g e1; g e2
  | Tuple(es) | App(_, es) | Nary(_, es)-> List.iter g es

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

let e_find (type t) f (e : t gexpr) = 
  let module E = struct exception Found of (t gexpr) end in
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

(* FIXME: is this sufficient? *)
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

let e_map_top f = 
  let tbl = He.create 103 in
  let rec aux e = 
    try He.find tbl e 
    with Not_found ->
      let e' = try check_fun f e with Not_found -> sub_map aux e in
      He.add tbl e e';
      e' in
  aux 

let e_replace e1 e2 = 
  e_map_top (fun e -> if e_equal e e1 then e2 else raise Not_found)

let e_subst s = e_map_top (fun e -> Me.find e s)

let se_of_list = List.fold_left (fun s e -> Se.add e s) Se.empty


type ctxt = Vsym.t * expr

let inst_ctxt (v, e') e = e_replace (mk_V v) e e'

let typeError_to_string (ty1,ty2,e1,me2,s) =
  match me2 with
  | Some e2 -> 
      format_to_string (fun fmt ->
        F.fprintf fmt "incompatible types `%a' vs. `%a' for expressions `%a' and `%a' in %s"
          pp_ty ty1 pp_ty ty2 pp_exp e1 pp_exp e2 s)
  | None when ty_equal ty1 ty2 ->
      format_to_string (fun fmt ->
        F.fprintf fmt "type error in `%a' of type %a: %s" pp_exp e1 pp_ty ty1 s)
  | None ->
      format_to_string (fun fmt ->
        F.fprintf fmt "expected type `%a', got  `%a' for Expression `%a': %s"
          pp_ty ty1 pp_ty ty2 pp_exp e1 s)

let catch_TypeError f =
  try f()
  with Constructors.TypeError(ty1,ty2,e1,me2,s) ->
    print_string (typeError_to_string (ty1,ty2,e1,me2,s));
    raise (Constructors.TypeError(ty1,ty2,e1,me2,s))

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
        List.split 
          (List.mapi (fun i _ -> aux (mk_Proj i e1) (mk_Proj i e2)) lt) in
      mk_Tuple es, mk_Tuple zs in
  let x1 =  Vsym.mk "x"  t in
  let x2 = Vsym.mk "x" t in
  let e, z = aux (mk_V x1) (mk_V x2) in
  (x1,(x2,e)), z
    
let mk_Zero t = snd (sub t)

let rec is_Zero e = 
  match e.e_node with
  | Cnst (B false) -> true
  | Cnst (FNat 0) -> true
  | Cnst Z -> true
  | Tuple es -> List.for_all is_Zero es
  | App(GExp _, [e1;e2]) -> 
    is_Zero e2 || is_Zero e1
  | _ -> false


    
