(* Grobner basis computations for K[X]-module *)

(* Imports and abbreviations *)

    
open List;;
open Num;;
open NormField;;
  
(* ------------------------------------------------------------------------- *)
(*  Utility functions                                                        *)
(* ------------------------------------------------------------------------- *)
  
let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec lexord ord l1 l2 =
  match (l1,l2) with
    (h1::t1,h2::t2) -> if ord h1 h2 then length t1 = length t2
                       else h1 = h2 && lexord ord t1 t2
  | _ -> false;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;


let rec distinctpairs l =
  match l with
   x::t -> itlist (fun y a -> (x,y) :: a) t (distinctpairs t)
  | [] -> [];;


  
(* ------------------------------------------------------------------------- *)
(* Defining polynomial types                                                 *)
(* ------------------------------------------------------------------------- *)

type mon = Num.num * int list;;

type pol = mon list;;

type i_var_set = int list;;


  
(* ------------------------------------------------------------------------- *)
(* Conversions functions                                                     *)
(* ------------------------------------------------------------------------- *)



let ipoly_to_poly vars (p:Poly.ipoly) : pol =
  let pol = Poly.IP.to_terms p in
  map (fun (m,c) -> (num_of_big_int c, mapi (fun i _ -> try assoc (i+1) m
                                                        with Not_found -> 0
                                            ) vars  )) pol;;

let poly_to_ipoly vars (p:pol) : Poly.ipoly =
  Poly.IP.from_terms @@ map (fun (c,m) -> ((map2 (fun pow t-> (t,pow)) m vars, ((big_int_of_num c)))) ) p;;
  
let eps_to_polys eps =
  let ipolys, mp = ep_to_ip eps in
  let vars = Hashtbl.fold (fun i _ acc -> i::acc) mp [] in
  map (ipoly_to_poly vars) ipolys,vars,mp;;
                                         
let polys_to_eps polys vars mp =
  let ipolys = map (poly_to_ipoly vars) polys in
  map (fun p -> import_ipoly "Groebner converter" p mp) ipolys ;;

  
(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let mmul ((c1,m1):mon) ((c2,m2):mon) :mon  = (c1*/c2,map2 (+) m1 m2);;

let mdiv (pvars:i_var_set)=
  let index_sub n1 n2 = if n1 < n2 then failwith "mdiv" else n1-n2 in
  fun ((c1,m1):mon) ((c2,m2):mon) -> let pows = map2 index_sub m1 m2 in
                                     let checker = List.combine pows pvars in
                         if (List.fold_left (fun  a (x,y) -> (y=1 && x>0)|| a ) false checker) then failwith "mdiv" else
                         ((c1//c2,pows):mon);;

let mlcm ((_,m1):mon) ((_,m2):mon) :mon= (Int 1,map2 max m1 m2);;
  
  
(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
  let n1 = itlist (+) m1 0 and n2 = itlist (+) m2 0 in
  n1 < n2 || n1 = n2 &&  lexord(>) m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)
let mpoly_mmul cm (pol:pol) :pol= map (mmul cm) pol;;

let mpoly_neg (pol:pol) :pol= map (fun (c,m) -> (minus_num c,m)) pol ;;



let rec mpoly_add (l1:pol) (l2:pol):pol =
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | ((c1,m1)::o1,(c2,m2)::o2) ->
        if m1 = m2 then
          let c = c1+/c2 and rest = mpoly_add o1 o2 in
          if c =/ Int 0 then rest else (c,m1)::rest
        else if morder_lt m2 m1 then (c1,m1)::(mpoly_add o1 l2)
        else (c2,m2)::(mpoly_add l1 o2);;

let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;


(* ------------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.       *)
(* ------------------------------------------------------------------------- *)

let reduce1 cm (pol,pvars) =
  match pol with
    [] -> failwith "reduce1"
  | hm::cms -> let c,m = mdiv pvars cm hm in mpoly_mmul (minus_num c,m) cms;;

(* ------------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                  *)
(* ------------------------------------------------------------------------- *)

let reduceb cm pols = tryfind (reduce1 cm) pols;;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).     *)
(* ------------------------------------------------------------------------- *)

let rec reduce pols pol =
  match pol with
    [] -> []
  | cm::ptl -> try reduce pols (mpoly_add (reduceb cm pols) ptl)
               with Failure _ -> cm::(reduce pols ptl);;

(* ------------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                  *)
(* ------------------------------------------------------------------------- *)

let spoly pol1 pol2 =
  let (pol1,pvar1)=pol1 and (pol2,pvar2) = pol2 in
  match (pol1,pol2) with
    ([],_) -> []
  | (_,[]) -> []
  | (m1::ptl1,m2::ptl2) ->
        let m = mlcm m1 m2 in
        mpoly_sub (mpoly_mmul (mdiv pvar1 m m1) ptl1)
                  (mpoly_mmul (mdiv pvar2 m m2) ptl2);;

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm for free multi-module                             *)
(* ------------------------------------------------------------------------- *)

let rec grobner basis pairs =
  (*print_string(string_of_int(length basis)^" basis elements and "^
               string_of_int(length pairs)^" pairs");
  print_newline();*)
  match pairs with
    [] -> basis
  | (p1,p2)::opairs ->
        try
          let sp = reduce basis (spoly p1 p2) in
        if sp = [] then grobner basis opairs
        (*else if for_all (for_all ()) sp then basis*) else
        let sp_pvars = map2 (fun x y -> x +y - x*y) (snd p1) (snd p2) in
        let newcps = map (fun p -> p,(sp,sp_pvars)) basis in
          grobner ((sp,sp_pvars)::basis) (opairs @ newcps)    
        with Failure _ -> grobner basis opairs;;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let groebner basis = grobner basis (distinctpairs basis);;


let is_in basis pol = (reduce basis pol = []);; 

