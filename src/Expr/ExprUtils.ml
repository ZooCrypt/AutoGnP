(*s Functions on expressions that do not require access to internals *)

(*i*)
open Expr
open Type
open Syms
open Abbrevs
open Util
(*i*)

let ty_prod_vs vs =
  match List.map (fun vs -> vs.Vsym.ty) vs with
  | [a] -> a
  | ts  -> mk_Prod ts

(*i ----------------------------------------------------------------------- i*)
(* \hd{Indicator functions} *)

let is_V e = match e.e_node with V _ -> true | _ -> false

let is_H e = match e.e_node with H _ -> true | _ -> false

let is_Quant q e = match e.e_node with Quant(q',_,_) when q=q' -> true | _ -> false
let is_SomeQuant e = match e.e_node with Quant(q,_,_) -> true | _ -> false
let is_All = is_Quant All and is_Exists = is_Quant Exists

let is_Tuple e = match e.e_node with Tuple _ -> true | _ ->  false

let is_Proj e = match e.e_node with Proj _ -> true | _ ->  false

let is_some_Cnst e = match e.e_node with Cnst _ -> true | _ -> false

let is_FNat e = match e.e_node with Cnst (FNat _) -> true | _ -> false

let is_FOne e = match e.e_node with Cnst (FNat 1) -> true | _ -> false

let is_FZ e = match e.e_node with Cnst (FNat 0) -> true | _ -> false

let is_Cnst c e = match e.e_node with Cnst c' -> c = c' | _ -> false

let is_ProjPermKey ke f e = match e.e_node with
  | ProjPermKey(ke', kp) when ke = ke' ->
     let kp_ty = mk_ty (KeyPair f.Psym.pid) in ty_equal kp.e_ty kp_ty
  | _ -> false
				     
let is_True e = is_Cnst (B true) e

let is_False e = is_Cnst (B false) e

let is_GGen e = is_Cnst GGen e

let is_GOne e = is_G e.e_ty && e_equal e (mk_GOne (destr_G e.e_ty))

let is_some_App e = match e.e_node with App _ -> true | _ -> false

let is_App o e = match e.e_node with App(o',_) -> o = o' | _ -> false

let is_Perm e =  match e.e_node with
  | App(o',_) ->
     (match o' with
       | Perm _ -> true
       | _ -> false)
  | _ -> false

let is_FDiv e = is_App FDiv e

let is_FOpp e = is_App FOpp e

let is_Ifte e = is_App Ifte e

let is_GExp e = match e.e_node with App(GExp _,_) -> true | _ -> false

let is_some_Nary e = match e.e_node with Nary _ -> true | _ -> false

let is_Nary o e = match e.e_node with Nary(o',_) -> o' = o | _ -> false

let is_FPlus e = is_Nary FPlus e

let is_FMult e = is_Nary FMult e

let is_Xor e = is_Nary Xor e

let is_Land e = is_Nary Land e

let is_GLog e = match e.e_node with App(GLog _, _) -> true | _ -> false

let is_GLog_gv gv e =
  match e.e_node with App(GLog gv', _) -> Groupvar.equal gv gv' | _ -> false

let is_Eq e = is_App Eq e

let is_Not e = is_App Not e

let is_field_op = function
  | FOpp | FMinus | FInv | FDiv -> true
  | GExp _ | GLog _ | GInv | EMap _ | Perm _
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

let pp_sort_expensive = ref false

let pp_number_tuples = ref false

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

let pp_binder fmt (vs,o) =
  let l_paren,r_paren =
    match vs with
    | [v] -> "",""
    | _ -> "(",")" in
  F.fprintf fmt "%s%a%s in L_%a" l_paren (pp_list "," Vsym.pp) vs r_paren Oracle.pp o

(** Pretty-prints expression assuming that
    the expression above is of given type. *)
let rec pp_exp_p ~qual above fmt e =
  match e.e_node with
  | V(v)       -> 
    (* F.fprintf fmt "%a.%i" Vsym.pp v (Vsym.hash v) *)
    F.fprintf fmt "%a" (Vsym.pp_qual ~qual) v
  | H(h,e)     -> 
    F.fprintf fmt "@[<hov>%a(%a)@]" Hsym.pp h (pp_exp_p ~qual PrefixApp) e
  | ProjPermKey(ke,kp) -> F.fprintf fmt "@[<hov>get_%s(%a)@]"
                                    (if ke = PKey then "pk" else "sk")
                                    (pp_exp_p ~qual PrefixApp) kp
  | Tuple(es) -> 
    let pp_entry fmt (i,e) =
      F.fprintf fmt "%i := %a" i (pp_exp_p ~qual Tup) e
    in
    let pp fmt es =
      if !pp_number_tuples then
        F.fprintf fmt "@[<hov>%a@]"
          (pp_list ",@\n" pp_entry)
          (num_list es)
      else
        F.fprintf fmt "@[<hov>%a@]"
          (pp_list ",@," (pp_exp_p ~qual Tup))
          es
    in
    pp_maybe_paren false (above <> PrefixApp) pp fmt es
  | Quant(q,b,e) ->
     F.fprintf fmt "%s (%a): %a" (if q = All then "forall" else "exists")
               pp_binder b (pp_exp_p ~qual Top) e
  | Proj(i,e)  -> 
    F.fprintf fmt "(%a%s%i)" (pp_exp_p ~qual Tup) e "#" i
  | Cnst(c)    -> pp_cnst fmt c e.e_ty
  | App(o,es)  -> pp_op_p ~qual above fmt (o,es) 
  | Nary(o,es) ->
    let es =
      if !pp_sort_expensive then (
        L.map (fun e -> (e, fsprintf "%a" (pp_exp_p ~qual Top) e)) es
        |> L.sort (fun (e1,s1) (e2,s2) ->
             let cmp = compare s1 s2 in
             if cmp<>0 then cmp else e_compare e1 e2)
        |> L.map fst
      ) else (
        es
      )
    in
    pp_nop_p ~qual above fmt (o,es)

(** Pretty-prints operator assuming that
    the expression above is of given type. *)
and pp_op_p ~qual above fmt (op, es) =
  let pp_bin p op ops a b =
    let pp fmt () = 
      F.fprintf fmt ("@[<hv>%a"^^ops^^"%a@]")
        (pp_exp_p ~qual (Infix(op,0))) a
        (pp_exp_p ~qual (Infix(op,1))) b in
    pp_maybe_paren true p pp fmt ()
  in
  let pp_prefix op before after a =
    F.fprintf fmt "%s%a%s" before (pp_exp_p ~qual (Infix(op,0))) a after
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
    F.fprintf fmt "@[<hov>log(%a)@]" (pp_exp_p ~qual PrefixApp) a
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
    let ppe i = pp_exp_p ~qual (Infix(EMap es,i)) in
    F.fprintf fmt "e(%a,%a)" (ppe 0) a (ppe 1) b
  | Perm(ptype,f), [proj_ke;arg] -> F.fprintf fmt
     "%a%s(%a,%a)" Psym.pp f (if ptype = IsInv then "_inv" else "")
                   (pp_exp_p ~qual above) proj_ke (pp_exp_p ~qual above) arg
  | Ifte, [a;b;d] ->
    let ppe i = pp_exp_p ~qual (Infix(Ifte,i)) in
    let pp fmt () =
      F.fprintf fmt "@[<hv>%a?%a:%a@]" (ppe 0) a (ppe 1) b (ppe 2) d
    in
    pp_maybe_paren true (notsep above) pp fmt ()
  | GInv, [a] ->
    pp_prefix GInv  ""      "^-1" a
  | _             -> failwith "pp_op: invalid expression"

(** Pretty-prints n-ary operator assuming that
    the expression above is of given type. *)
and pp_nop_p ~qual above fmt (op,es) =
  let pp_nary hv op ops p =
    pp_maybe_paren hv p (pp_list ops (pp_exp_p ~qual (NInfix(op)))) fmt es
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
let pp_exp fmt e = pp_exp_p ~qual:Unqual Top fmt e
let pp_exp_qual ~qual fmt e = pp_exp_p ~qual Top fmt e
let pp_op  fmt x = pp_op_p ~qual:Unqual Top fmt x
let pp_nop fmt x = pp_nop_p ~qual:Unqual Top fmt x

(** Pretty-printing without parens around tuples. *)
let pp_exp_tnp fmt e = pp_exp_p ~qual:Unqual PrefixApp fmt e

let pp_ctxt fmt (v,e) = 
  F.fprintf fmt "@[<hov>(%a ->@ %a)@]" Vsym.pp v pp_exp e 
(*i ----------------------------------------------------------------------- i*)
(* \hd{Destructor functions} *)

exception Destr_failure of string

let destr_V e = match e.e_node with V v -> v | _ -> raise (Destr_failure "V")

let destr_H e = 
  match e.e_node with H(h,e) -> (h,e) | _ -> raise (Destr_failure "H")

let destr_Perm e =
  match e.e_node with
  | App(o,[k;e]) ->
     (match o with
      | Perm(ptype,f) -> (f,ptype,k,e)
      | _ -> raise (Destr_failure "Perm"))
  | _ -> raise (Destr_failure "Perm")

let destr_ProjPermKey e =
  match e.e_node with
  | ProjPermKey (ke,kp) -> (ke,kp)
  | _ -> raise (Destr_failure "ProjPermKey")

let destr_Quant e = 
  match e.e_node with Quant(q,b,e) -> (q,b,e) | _ -> raise (Destr_failure "Quant")
                                                           
let destr_All e = 
  match e.e_node with Quant(All,b,e) -> (b,e) | _ -> raise (Destr_failure "forall")
                                                           
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
  | _ -> raise (Destr_failure "GExp")

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

let is_InEq e = is_Not e && is_Eq (destr_Not e)

let destr_Ifte e = 
  match e.e_node with 
  | App(Ifte,[a;b;c]) -> (a,b,c) 
  | _ -> raise (Destr_failure "Ifte")


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
    | ProjPermKey(ke,kp) -> go ie kp; run e0
    | H(_,e) | Proj(_,e) | Quant(_,_,e)-> 
      go ie e; run e0
    | Tuple(es) | App(_,es) | Nary(_,es) ->
      L.iter (go ie) es;  run e0
  in
  go false e0

let e_vars = e_find_all is_V
let e_hash_calls = e_find_all is_H                        

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
      pp_ty ty2 pp_ty ty1 pp_exp e1 s

let catch_TypeError f =
  try f()
  with TypeError(ty1,ty2,e1,me2,s) ->
    print_string (typeError_to_string (ty1,ty2,e1,me2,s));
    raise (TypeError(ty1,ty2,e1,me2,s))

let se_of_list = L.fold_left (fun s e -> Se.add e s) Se.empty

let he_keys he = He.fold (fun k _ s -> Se.add k s) he Se.empty

let se_disjoint s1 s2 = Se.is_empty (Se.inter s1 s2)

let me_of_list es = L.fold_left (fun s (k,v) -> Me.add k v s) Me.empty es

let he_to_list he = He.fold (fun k v l -> (k,v)::l) he []

type ctxt = Vsym.t * expr

let ctxt_ty (v,e) = v.Vsym.ty, e.e_ty 

let inst_ctxt (v, e') e = e_replace (mk_V v) e e'

let sub t = 
  let rec aux e1 e2 = 
    match e2.e_ty.ty_node with (* FIXME *) (* TODO : Permutations handling *)
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
  let x1 = Vsym.mk "x" t in
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

let insert_Land e1 e2 =
  let ty_Bool = mk_ty Bool in
  if( not(ty_equal e1.e_ty ty_Bool) ) then
    raise (TypeError(e1.e_ty, ty_Bool, e1, None,
                     "insert_Land failed, expr of type Bool expected."));
  match e2.e_node with
  | Nary(Land,es) -> mk_Land (e1::es)
  | _ -> mk_Land [e1;e2]
                 
type inverter = I of expr

let expr_of_inverter (I e) = e

let pp_inverter fmt i = pp_exp fmt (expr_of_inverter i)

let rec e_eq_remove_eventual_perms e =
  let e1,e2 = destr_Eq e in
  ( try
    let ( (f1,ptype1,k1,e11), (f2,ptype2,k2,e22) ) =
      destr_Perm e1, destr_Perm e2 in
    if (Psym.equal f1 f2 && ptype1 = ptype2 && e_equal k1 k2)
    then e_eq_remove_eventual_perms (mk_Eq e11 e22)
    else e
  with
  | Destr_failure _ -> e )

let eqs_equal e1 e2 =
  let ((e11,e12),(e21,e22)) = (destr_Eq e1,destr_Eq e2) in
  (e_equal e11 e21 && e_equal e12 e22) ||
    (e_equal e12 e21 && e_equal e11 e22)
                        
let rec e_equivalent_eqs ?strong:(strong = true) e1 e2 =
  if (is_Eq e1 && is_Eq e2) then (
    let e1' = e_eq_remove_eventual_perms e1
    and e2' = e_eq_remove_eventual_perms e2 in
    let ((e11,e12),(e21,e22)) = (destr_Eq e1',destr_Eq e2') in
    if strong && (is_Perm e11 <> is_Perm e12) && (is_Perm e21 <> is_Perm e22)
    then (
      let ((f1,ptype1,k1,e11),e12) =
        if is_Perm e11 then (destr_Perm e11,e12)
        else (destr_Perm e12, e11)
      and ((f2,ptype2,k2,e21),e22) =
        if is_Perm e21 then (destr_Perm e21,e22)
        else (destr_Perm e22, e21) in
      if (ptype1 <> ptype2) then
        e_equivalent_eqs ~strong:false (mk_Eq e11 (mk_Perm f1 ptype2 k1 e12)) e2'
      else
        eqs_equal e1' e2'
    ) else
      eqs_equal e1' e2'
  ) else
    e_equal e1 e2
