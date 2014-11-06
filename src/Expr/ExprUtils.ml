(*s Functions on expressions that do not require access to internals *)

(*i*)
open Expr
open Type
open Syms
open Abbrevs
open Util
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Indicator functions} *)

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

let is_GExp e = match e.e_node with App(GExp _,_) -> true | _ -> false

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
(* \hd{Pretty printing} *)

(** The term $*(+(a,b),c)$ can be printed as $(a + b) * c$
    or $a + b * c$.
    We pass enough information to the function call
    printing $a + b$ to decide if parentheses are
    required around this expression or not.
*)

(** Pretty print constant. *)
let pp_cnst fmt c ty =
  match c with
  | GGen   -> if Groupvar.name (destr_G ty) <> ""
              then F.fprintf fmt "g_%a" Groupvar.pp (destr_G ty)
              else F.fprintf fmt "g"
  | FNat n -> F.fprintf fmt "%i" n
  | Z      -> F.fprintf fmt "0%%%a" pp_ty ty
  | B b    -> F.fprintf fmt "%b" b

(** Constructor above the current expression. *)
type 'a above =
    PrefixApp          (*r prefix function application: $f(\ldots)$ *)
  | Top                (*r topmost, nothing above *)
  | Infix  of op * int (*r infix operator, i-th argument *)
  | NInfix of nop      (*r n-ary infix operator *)
  | Tup                (*r tuple constructor *)

(** Above does not have separators that allow to leave out parentheses. *)
let notsep above = above <> Top && above <> PrefixApp && above <> Tup

(** Surround with an [hv] or [hov] box. *)
let pp_box hv pp fmt =
  if hv
  then F.fprintf fmt "@[<hv>%a@]" pp
  else F.fprintf fmt "@[<hov>%a@]" pp

(** Enclose with given format strings. *)
let pp_enclose hv ~pre ~post pp fmt x =
  F.fprintf fmt "%(%)%a%(%)" pre (pp_box hv pp) x post

(** Enclose with parens. *)
let pp_paren hv = pp_enclose hv ~pre:"(" ~post:")"

(** Enclose with parens depending on boolean argument. *)
let pp_maybe_paren hv c = pp_if c (pp_paren hv) (pp_box hv)

(** Pretty-prints expression assuming that
    the expression above is of given type. *)
let rec pp_exp_p above fmt e =
  match e.e_node with
  | V(v)       -> 
    (* F.fprintf fmt "%a.%i" Vsym.pp v (Vsym.hash v) *)
    F.fprintf fmt "%a" Vsym.pp v
  | H(h,e)     -> 
    F.fprintf fmt "@[<hov>%a(%a)@]" Hsym.pp h (pp_exp_p PrefixApp) e
  | Tuple(es)  -> 
    let pp fmt = F.fprintf fmt "@[<hov>%a@]" (pp_list ",@," (pp_exp_p Tup)) in
    pp_maybe_paren false (above <> PrefixApp) pp fmt es
  | Proj(i,e)  -> 
    F.fprintf fmt "%a%s%i" (pp_exp_p Tup) e "\\" i
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

(** Pretty-prints operator assuming that
    the expression above is of given type. *)
and pp_op_p above fmt (op, es) =
  let pp_bin p op ops a b =
    let pp fmt () = 
      F.fprintf fmt ("@[<hv>%a"^^ops^^"%a@]")
        (pp_exp_p (Infix(op,0))) a
        (pp_exp_p (Infix(op,1))) b in
    pp_maybe_paren true p pp fmt ()
  in
  let pp_prefix op before after a =
    F.fprintf fmt "%s%a%s" before (pp_exp_p (Infix(op,0))) a after
  in
  match op, es with
  | GExp _,   [a;b] -> 
    pp_bin (notsep above && above<>NInfix(GMult) && above<>NInfix(GMult)
            && above<>Infix(Eq,0) && above<>Infix(Eq,1))
      op "^" a b
  | FDiv,   [a;b] -> 
    pp_bin (notsep above) FDiv "@ / " a b
  | FMinus, [a;b] -> 
    pp_bin (notsep above && above<>Infix(FMinus,0)) FMinus "@ - " a b
  | Eq,     [a;b] -> 
    pp_bin (notsep above && above<>NInfix(Land)) Eq "@ = " a b
  | GLog _, [a]   ->
    F.fprintf fmt "@[<hov>log(%a)@]" (pp_exp_p PrefixApp) a
  | FOpp,   [a]   ->
    pp_prefix FOpp  "-"     ""    a
  | FInv,   [a]   -> 
    pp_prefix FInv  ""      "^-1" a
  | Not,    [a]   ->
    begin match a.e_node with
    | App(Eq,[e1;e2]) ->
      pp_bin (notsep above && above<>NInfix(Land)) Eq "@ <> " e1 e2
    | _ ->
      pp_prefix Not   "not "  ""    a
    end
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

(** Pretty-prints n-ary operator assuming that
    the expression above is of given type. *)
and pp_nop_p above fmt (op,es) =
  let pp_nary hv op ops p =
    pp_maybe_paren hv p (pp_list ops (pp_exp_p (NInfix(op)))) fmt es
  in
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

(** Pretty-print expressions/operators assuming they are topmost. *)
let pp_exp fmt e = pp_exp_p Top fmt e
let pp_op  fmt x = pp_op_p  Top fmt x
let pp_nop fmt x = pp_nop_p Top fmt x

(** Pretty-printing without parens around tuples. *)
let pp_exp_tnp fmt e = pp_exp_p PrefixApp fmt e

(*i ----------------------------------------------------------------------- i*)
(* \hd{Destructor functions} *)

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

let destr_Ifte   e = 
  match e.e_node with 
  | App(Eq,[a;b;c]) -> (a,b,c) 
  | _ -> raise (Destr_failure "Ifte")

let destr_Exists  e = 
  match e.e_node with
  | Exists(e1,e2,vh) -> e1,e2,vh
  | _ -> raise (Destr_failure "Exists")

let destr_Xor_nofail e = 
  match e.e_node with
  | Nary(Xor,es) -> es 
  | _ -> [e] 

let destr_Land_nofail e =
  match e.e_node with
  | Nary(Land,es) -> es 
  | _ -> [e] 

let destr_Tuple_nofail e =
  match e.e_node with
  | Tuple(es) -> es 
  | _ -> [e] 


(*i ----------------------------------------------------------------------- i*)
(* \hd{Useful functions on [expr]} *)

let e_iter_ty_maximal ty g e0 = 
  let rec go ie e0 =
    (* me = e is a maximal expression of the desired type *)
    let me = not ie && ty_equal e0.e_ty ty in
    (* ie = immediate subterms of e inside a larger expression of the desired type *)
    let ie = me || (ie && ty_equal e0.e_ty ty) in
    let run = if me then g else fun _ -> () in
    match e0.e_node with
    | V(_) | Cnst(_)  -> ()
    | H(_,e) | Proj(_,e) -> 
      go ie e; run e0
    | Tuple(es) | App(_,es) | Nary(_,es) ->
      L.iter (go ie) es;  run e0
    | Exists(e1,e2,_) ->
      go ie e1; go ie e2; run e0
  in
  go false e0

let e_ty_outermost ty e =
  let res = ref [] in
  let rec go not_inside_type e =
    let right_type = Type.ty_equal e.e_ty ty in
    if not_inside_type && right_type  && not (L.mem e !res) then
      res := e::!res
    else
      e_sub_iter (go (not right_type)) e
  in
  go true e;
  L.rev !res

let e_vars = e_find_all is_V

let has_log e = e_exists (fun e -> is_GLog e) e

let is_ppt e = not (has_log e)

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

let se_of_list = L.fold_left (fun s e -> Se.add e s) Se.empty

let me_of_list es = L.fold_left (fun s (k,v) -> Me.add k v s) Me.empty es

type ctxt = Vsym.t * expr

let inst_ctxt (v, e') e = e_replace (mk_V v) e e'

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
