module type Tagged = sig
  type t
  val tag : t -> int
end

module type OrderedHash =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHash (X : Tagged) : OrderedHash with type t = X.t = struct
  type t = X.t
  let hash t = X.tag t
  let equal t1 t2 = X.tag t1 = X.tag t2 (* FIXME: is there really a speedup using == on int *)
  let compare t1 t2 = Pervasives.compare (X.tag t1) (X.tag t2)
end

module StructMake (X:Tagged) =
  struct
    module T = OrderedHash(X)
    module M = Map.Make(T)
    module S = Set.Make(T)
    module H = Hashtbl.Make(T)
end

module Ints = StructMake (struct
  type t = int
  let tag x = x
end)

module Mint = Ints.M
module Sint = Ints.S
module Hint = Ints.H

let unique_int () = Oo.id (object end)

(* ----------------------------------------------------------------------- *)

let list_eq_for_all2 f l1 l2 =
  try List.for_all2 f l1 l2 with _ -> false

let smart_map f l =
  let rec aux r l' = 
    match l' with
    | [] -> l
    | hd::tl -> 
        let hd' = f hd in
        if hd == hd' then aux (hd::r) tl
        else List.rev_append r (hd' :: List.map f tl) in
  aux [] l

let rec drop i l =
  match l with
  | _::xs when i > 0 -> drop (i - 1) xs
  | _ -> l

let rec take i l =
  match l with
  | x::xs when i > 0 -> x::(take (i - 1) xs)
  | _ -> []

let list_from_to i j = (* [i,j), i.e., excluding j *)
  let rec go aux i = if i >= j then aux else go (i::aux) (i+1)
  in List.rev (go [] i)

let (|>) x f = f x

let format_to_string f = 
  ignore (Format.flush_str_formatter ());
  f Format.str_formatter;
  Format.flush_str_formatter ()

let fsprintf fm = Format.fprintf Format.str_formatter fm

let fsget _ = Format.flush_str_formatter ()

let compare_on f x y = compare (f x) (f y)

let exc_to_opt f = try Some (f ()) with _ -> None

let map_opt f m = match m with
  | Some x -> Some (f x)
  | None -> None

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> Format.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let pp_list_c pe = (pp_list "," pe)
let pp_list_s = pp_list_c (fun fmt -> Format.fprintf fmt "%s")