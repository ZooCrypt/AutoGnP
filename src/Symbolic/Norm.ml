open Type
open Expr

(* For a list of tvsymbols [l1;..;lk], return projection types
   ([], l1, [l2;..;lk]), .., ([l1,..,lk-1], lk, []) *)
let base_projs ty =
  let rec go left right = match right with
    | []      -> []
    | x :: xs -> (mk_ty left, mk_ty [x], mk_ty xs)::(go (left @ [x]) xs)
   in go [] ty.ty_sum

(* split a given expression 'a' into a list 'as' of expressions of basic types such that
   mk_lapp as =_E a *)
let split_basic_type e =
  if is_ty_var e.e_ty then [e]
  else List.map (fun pt -> mk_Proj pt e) (base_projs e.e_ty)

(* Replace all applications of xor/proj to bitstrings of
   non-basic length with concatenations of xor/proj applied to
   projections to basic lengths (see `test_xor_base_type`). *)
let rec xor_proj_basic_type e0 =
  let e = e_sub_map xor_proj_basic_type e0 in
  match e.e_node, e.e_ty with
  | Xor(a,b), ty when not (is_ty_var ty) ->
      let xor_proj pt = mk_Xor (mk_Proj pt a) (mk_Proj pt b) in
      mk_App (List.map xor_proj (base_projs ty))
  | Proj((l',_m,r'),a), ty when not (is_ty_var ty) -> (* _m = e.e_ty *)
      mk_App (List.map (fun (l,m,r) ->
      	                  mk_Proj (ty_concat l' l, m, ty_concat r r') a)
                        (base_projs ty))
  | _ -> e


let rec xor_to_list e0 = match e0.e_node with
  | Z           -> []
  | Xor(a,b)    -> xor_to_list a @ xor_to_list b
  | _           -> [e0]

let rec list_to_xor ts ty = match ts with
  | t::(x::xs) -> mk_Xor t (list_to_xor (x::xs) ty)
  | x::[]      -> x
  | []         -> mk_Z ty

let se_of_list l = List.fold_left (fun x s -> Se.add s x) Se.empty l

let xor_to_set e = se_of_list (xor_to_list e)


(* [norm_proj l m e] computes the normal form of a projection of e with left type l
    and result type m. The right type can be computed as [l + m - e.e_ty]. *)
let rec norm_proj l m e =
  let rec app_take l m acc es =
    let ll,lm = l.ty_sum, m.ty_sum in
    match es with
    | y::ys -> let ly = y.e_ty.ty_sum in
               let len_y = List.length ly in
               if List.length (ll @ lm) <= List.length ly
               then (l,acc@[y]) (* y contains part *)
               else
                 let l' = mk_ty (Util.drop len_y ll) in
                 (if List.length ly <= List.length ll
                  (* no part contained in y *)
                  then app_take l' m acc       ys
                  (* some part contained in y and some in ys *)
                  else app_take l' m (acc@[y]) ys)
    | [] -> (l,acc)
  in
  (* smart projection constructor *)
  let make_proj l m e =
    let l_lm  = (ty_concat l m).ty_sum in
    let l_all = e.e_ty.ty_sum in
    let l_r = Util.drop (List.length l_lm) l_all in
    if List.length l.ty_sum = 0 && List.length l_r = 0
    then e else mk_Proj (l, m, mk_ty l_r) e
  in
  match e.e_node with
  | Z -> mk_Z m
  (* use [ [e']_l'^m') ]_l^m) = [e']_(l'+l)^m *)
  | Proj ((l',_,_), e') -> norm_proj (ty_concat l' l) m e'
  (* remove redundant expressions on the left and right in App *)
  | App es -> (match app_take l m [] es with
               | (l',[e]) -> norm_proj l' m e
               | (l',es)  -> make_proj l' m (mk_App es))
  | _ -> make_proj l m e

let rec norm1 e0 =
  let e0 = e_sub_map norm1 e0 in
  let rec mod2 xs = match xs with
    | x::y::ys when e_equal x y -> mod2 ys
    | x::y::ys                  -> x::(mod2 (y::ys))
    | _                         -> xs
  in
  let rec merge_adjacent xs = match xs with
    | x::y::ys ->
        begin
          match x.e_node, y.e_node with
          | Proj((l,m,_r),a), Proj((l',m',_r'),a')
            when e_equal a a' && ty_equal (ty_concat l m) l' ->
             merge_adjacent ((norm_proj l (ty_concat m m') a)::ys)
          (* why merge adjacent zeros? *)
          (* | Z, Z -> merge_adjacent (mk_z (ty_concat x.e_ty y.e_ty)::ys) *)
          | _ -> x::(merge_adjacent (y::ys))
        end
    | _  -> xs
  in
  (* If [e] is a projection, split projection to basic, otherwise keep as is. *)
  let proj_basic e = match e.e_node, e.e_ty with
    | Proj((l,_m,r),e'), ty when not (is_ty_var ty) ->
        let rec go l' r' = match r' with
          | [] -> []
          | tv::tvs -> (mk_Proj (ty_concat l (mk_ty l'),
                                 mk_ty [tv],
                                 ty_concat (mk_ty tvs) r)
                                e'):: go (l'@[tv]) tvs
        in go [] ty.ty_sum
    | _ -> [e]
  in
  let rec getApp x = match x.e_node with
    | App l -> List.concat (List.map getApp l)
    | _ -> [x]
  in
  match e0.e_node with
  | Z  | V(_) | H _ -> e0
  | P(f, e)   -> (match e.e_node with
                  | Pinv(f', e') when Psym.equal f f' -> e'
                  | _ -> e0)
  | Pinv(f,e) -> (match e.e_node with
                  | P(f', e') when Psym.equal f f' -> e'
                  | _ -> e0)
  | Xor _     -> let xs = xor_to_list e0 in
                 list_to_xor (mod2 (List.sort e_compare xs)) e0.e_ty
  | Proj((l,m,_r),e) -> norm_proj l m e
  | App l -> (match (List.concat (List.map proj_basic (merge_adjacent (List.concat (List.map getApp l))))) with
              | [ e' ] -> e'
              | es     -> mk_App es)

let norm e = norm1 (xor_proj_basic_type e)

