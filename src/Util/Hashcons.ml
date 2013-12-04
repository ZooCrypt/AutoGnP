
module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val tag : int -> t -> t
  end

module type S =
  sig
    type t
    val hashcons : t -> t
    val iter : (t -> unit) -> unit
(*  val stats : unit -> int * int * int * int * int * int *)
    val clear : unit -> unit
  end

module Make(H : HashedType) : (S with type t = H.t) =
  struct
    type t = H.t

    module WH = Hashtbl.Make (H)
(*    module WH = Weak.Make(H) *)

    let next_tag = ref 0

    let htable = WH.create 5003

    let merge tbl d = 
(*      WH.merge tbl d  *)
      try WH.find tbl d 
      with Not_found ->
        WH.add tbl d d;
        d 

    let hashcons d =
      let d = H.tag !next_tag d in
      let o = merge htable d in
      if o == d then incr next_tag;
      o

    let iter f = WH.iter (fun k _ -> f k) htable

(*  let stats () = WH.stats htable *)
    let clear () = WH.clear htable 
  end

let combine acc n = n * 65599 + acc
let combine2 acc n1 n2 = combine acc (combine n1 n2)
let combine_list f = List.fold_left (fun acc x -> combine acc (f x))
