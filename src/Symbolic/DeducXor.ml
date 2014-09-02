(*s Deducibility for XOR expressions. *)

(*i*)
open Expr
open Util
open Type
open Syms
(*i*)

module Ht = Hashtbl
module L = List

let direct_subterms o s es = 
  let go acc e =
    match e.e_node with
    | Nary(o',es') when o = o' ->
      Se.union acc (se_of_list es')
    | _ ->
      Se.add e acc
  in
  List.fold_left go s es

let xor_to_vec rows bindings e =
  let arr = Array.make rows false in
  let set_idx e =
    Array.set arr (Ht.find bindings e) true
  in
  (match e.e_node with
   | Nary(Xor,es') ->
     List.iter set_idx es'
   | _ ->
     set_idx e);
  arr

let solve_xor ecs e =
  let es     = L.map snd ecs in
  let es_sts = direct_subterms Xor Se.empty es in
  let rows   = Se.cardinal es_sts in
  let e_sts  = direct_subterms Xor Se.empty [e] in
  if (not (Se.subset e_sts es_sts)) then raise Not_found; 
  let bindings  = Ht.create rows in
  let ibindings = Ht.create rows in  
  List.iteri
    (fun i e ->
       Ht.add bindings e i;
       Ht.add ibindings i e)
    (Se.elements es_sts);
  let colvecs = List.map (xor_to_vec rows bindings) es in
  let vec = xor_to_vec rows bindings e in
  let msolvec = LinAlg.solve colvecs vec in
  let cs = L.map fst ecs in
  let ctxt =
    match msolvec with
    | None -> raise Not_found
    | Some(solvec) ->
        mk_Xor
          (cat_Some
            (L.map2 (fun b_i ct -> if b_i then Some ct else None) solvec cs))
  in
  ctxt

let _test_solve_xor_1 () =
  let l = Lenvar.mk "l" in
  let t = mk_BS l in
  let vx = Vsym.mk "x" t in
  let vz = Vsym.mk "z" t in
  let (x,z) = (mk_V vx, mk_V vz) in
  let a = mk_Xor [x] in
  let b = mk_Xor [x;z] in  
  let c = mk_Xor [z] in
  let p1 = mk_V (Vsym.mk "p1" t) in
  let p2 = mk_V (Vsym.mk "p2" t) in  
  let c = solve_xor [(p1,a); (p2,b)] c in
  failwith (fsprintf "Deduced context %a\n%!" pp_exp c)

let _test_solve_xor_2 () =
  let l = Lenvar.mk "l" in
  let t = mk_BS l in
  let vx = Vsym.mk "x" t in
  let vy = Vsym.mk "y" t in  
  let vz = Vsym.mk "z" t in
  let (x,y,z) = (mk_V vx, mk_V vy, mk_V vz) in
  let a = mk_Xor [x;y] in
  let b = mk_Xor [x;z] in  
  let c = mk_Xor [y;z] in
  let p1 = mk_V (Vsym.mk "p1" t) in
  let p2 = mk_V (Vsym.mk "p2" t) in  
  let c = solve_xor [(p1,a); (p2,b)] c in
  failwith (fsprintf "Deduced context %a\n%!" pp_exp c)

let _test_solve_xor_3 () =
  let l = Lenvar.mk "l" in
  let t = mk_BS l in
  let vx = Vsym.mk "x" t in
  let vy = Vsym.mk "y" t in  
  let vz = Vsym.mk "z" t in
  let (x,y,z) = (mk_V vx, mk_V vy, mk_V vz) in
  let a = mk_Xor [x;y] in
  let b = mk_Xor [x;z] in  
  let c = mk_Xor [y] in
  let d = mk_Xor [z] in
  let p1 = mk_V (Vsym.mk "p1" t) in
  let p2 = mk_V (Vsym.mk "p2" t) in  
  let p3 = mk_V (Vsym.mk "p3" t) in    
  let s = solve_xor [(p1,a); (p2,b); (p3,c)] d in
  failwith (fsprintf "3. Deduced context %a\n%!" pp_exp s)

