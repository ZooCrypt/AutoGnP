(* * Symbols for variables and other objects *)

(* ** Imports *)
open Abbrevs
open Util
open Id
open Type

(* ** Oracle Symbols
 * ----------------------------------------------------------------------- *)

module Osym = struct
  type t = { 
    id    : Id.id;
    dom   : ty;
    codom : ty;
  }

  let hash os = Id.hash os.id 
  let equal : t -> t -> bool = (==)
  let compare (x : t) (y : t) = hash x - hash y

  type tt = t
  module Os = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = Os.M
  module S = Os.S
  module H = Os.H

  let mk name dom codom = 
    { id = Id.mk name; dom = dom; codom = codom }

  let pp fmt os = F.fprintf fmt "%s" (Id.name os.id)
  let pp_long fmt os =
    F.fprintf fmt "%s : %a -> %a" (Id.name os.id) pp_ty os.dom pp_ty os.codom
  let to_string os = Id.name os.id
end

(* ** Qualified Symbols
 * ----------------------------------------------------------------------- *)

type 'a qual = Unqual | Qual of 'a

let map_qual f = function
  | Unqual -> Unqual
  | Qual x -> Qual (f x)

(* ** Variable Symbols
 * ----------------------------------------------------------------------- *)

module Vsym = struct

  type t = { 
    id : id;
    qual : Osym.t qual; (*r we allow qualified variables for eq-Hybrid-oracles *)
    ty : ty;
  }

  type tt = t

  let hash ps = Id.hash ps.id
  let equal : t -> t -> bool = (==)
  let compare (x : t) (y : t) = hash x - hash y

  module Ps = StructMake (struct
    type t = tt
    let tag = hash
  end)

  module M = Ps.M
  module S = Ps.S
  module H = Ps.H

  let mk name ty = { id = Id.mk name; qual = Unqual; ty = ty; }
  let mk_qual name qual ty = { id = Id.mk name; qual = qual; ty = ty; }

  let pp_tag fmt _t =
    pp_string fmt ""
    (* F.fprintf fmt ".%i" t *)

  let pp_qual ?qual:(qual=Unqual) fmt vs =
    let qual_eq o =
      match qual with
      | Unqual  -> false
      | Qual o' -> Osym.equal o o'
    in
    match vs.qual with
    | Unqual ->
      F.fprintf fmt "%s%a" (Id.name vs.id) pp_tag (Id.tag vs.id)
    | Qual o when qual_eq o ->
      F.fprintf fmt "%s%a" (Id.name vs.id) pp_tag (Id.tag vs.id)
    | Qual q ->
      F.fprintf fmt "%s`%s%a" (Id.name q.Osym.id) (Id.name vs.id) pp_tag (Id.tag vs.id)
  
  let pp fmt = pp_qual ~qual:Unqual fmt

  let to_string ps = Id.name ps.id
  let set_of_list l =
    L.fold_right
      (fun vs acc -> S.add vs acc)
      l
      S.empty
end

(* ** Adversary Symbols
 * ----------------------------------------------------------------------- *)

module Asym = struct
  type t = { 
    id : Id.id;
    dom : ty;
    codom : ty;
  }

  type tt = t

  let hash asym = Id.hash asym.id 
  let equal : t -> t -> bool = (==)
  let compare (x : t) (y : t) = hash x - hash y

  module As = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = As.M
  module S = As.S
  module H = As.H

  let mk name dom codom = 
    { id = Id.mk name; dom = dom; codom = codom }

  let pp fmt asym = F.fprintf fmt "%s" (Id.name asym.id)
  let pp_long fmt asym =
    F.fprintf fmt "%s : %a -> %a" (Id.name asym.id) pp_ty asym.dom pp_ty asym.codom
  let to_string os = Id.name os.id
end

(* ** Bilinear map symbols
 * ----------------------------------------------------------------------- *)
                            
module Esym = struct
  type t = { 
    id : Id.id;
    source1 : Groupvar.id;
    source2 : Groupvar.id;
    target  : Groupvar.id;
  }

  type tt = t

  let hash es = Id.hash es.id 
  let equal es1 es2 = Id.equal es1.id es2.id

  module Es = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = Es.M
  module S = Es.S
  module H = Es.H

  let mk name source1 source2 target =
    { id = Id.mk name; source1 = source1;
      source2 = source2; target = target }

  let pp fmt hs = F.fprintf fmt "%s" (Id.name hs.id)

  let name hs = Id.name hs.id
end

(* ** Permutation symbols
 * ----------------------------------------------------------------------- *)

module Psym = struct
  type t = { 
      id : Id.id;
      dom : ty;
      pid : Permvar.id;
  }

  type tt = t

  let hash ps = Id.hash ps.id 
  let equal ps1 ps2 = Id.equal ps1.id ps2.id

  module Ps = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = Ps.M
  module S = Ps.S
  module H = Ps.H

  let mk name dom pid =
    assert (name = Permvar.name pid);
    { id = Id.mk name; dom; pid}

  let pp fmt hs = F.fprintf fmt "%s" (Id.name hs.id)

  let name hs = Id.name hs.id
end

(* ** Function symbols
 * ----------------------------------------------------------------------- *)

module Hsym = struct
  type t = {
    id    : Id.id;
    ro    : bool;          (*r true if random oracle *)
    lkup  : bool;          (*r true is LookUp call in random oracle *)    
    dom   : ty;
    codom : ty;
  }

  type tt = t

  let hash hs = Id.hash hs.id 
  let equal hs1 hs2 = Id.equal hs1.id hs2.id

  module Hs = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = Hs.M
  module S = Hs.S
  module H = Hs.H

  let mk name ~ro ?lkup:(lkup=false) dom codom =
    { id = Id.mk name; ro; lkup = ro && lkup; dom; codom }

  let to_string hs = Id.name hs.id

  let is_ro hs = hs.ro
  let is_lkup hs = hs.ro && hs.lkup
  let pp fmt hs = F.fprintf fmt (if is_lkup hs then "m_%s" else "%s") (Id.name hs.id)
end

(* ** Random oracle symbols
 * ----------------------------------------------------------------------- *)

module Oracle = struct
  type t =
    | RO of Hsym.t
    |  O of Osym.t
              
  let mk_RO = function
    | h when Hsym.is_ro h -> RO h
    | h -> tacerror "mk_RO: (random) oracle expected, but %a is an operator" Hsym.pp h
  let mk_O o = O(o)

  type tt = t

  let hash = function
    | RO hs -> Hsym.hash hs
    |  O os -> Osym.hash os
                         
  let equal ors1 ors2 = match ors1,ors2 with
    | (RO hs1, RO hs2) -> Hsym.equal hs1 hs2
    | ( O os1,  O os2) -> Osym.equal os1 os2
    | _ -> false

                
  module Ors = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = Ors.M
  module S = Ors.S
  module H = Ors.H

  let mk name ~ro ?lkup:(lkup=false) dom codom =
    if ro then
      mk_RO(Hsym.mk name ~ro ~lkup dom codom)
    else
      mk_O(Osym.mk name dom codom)

  let pp fmt = function
    | RO hs -> Hsym.pp fmt hs
    |  O os -> Osym.pp fmt os
       
  let to_string = function
    | RO hs -> Hsym.to_string hs
    |  O os -> Osym.to_string os

  let is_ro = function
    | RO hs when Hsym.is_ro hs -> true
    | _ -> false

  let is_lkup = function
    | RO hs when Hsym.is_lkup hs -> true
    | _ -> false

  let get_id = function
    | RO hs -> hs.Hsym.id
    |  O os -> os.Osym.id
  let get_codom = function
    | RO hs -> hs.Hsym.codom
    |  O os -> os.Osym.codom
  let get_dom = function
    | RO hs -> hs.Hsym.dom
    |  O os -> os.Osym.dom
                 
  exception Destr_failure of string
                                      
  let destr_as_Hsym_t = function
    | RO hs -> hs
    | _ -> raise (Destr_failure "Oracle.destr_as_Hsym_t cast failure: received NON RANDOM Oracle")
  let destr_as_Osym_t = function
    | O os -> os
    | _ -> raise (Destr_failure "Oracle.destr_as_Osym_t cast failure: received RANDOM Oracle")
                 
end
		  
