(** This module defines types tagged with [int]s and some convenience functor applications
    for maps, sets, hashtables, lists, and pretty printing. *)

(** [tag] converts [t] into an [int]. The function must be injective. *)
module type Tagged = sig type t val tag : t -> int end

(** Ordered and hashable (to [int]) types.
    Equal [hash] does not have to imply that [equal] returns [true]. *)
module type OrderedHash =
  sig
    type t
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
  end

(** Create [OrderedHash] from [Tagged]. Assumes that the [tag] function is injective. *)
module OrderedHash :
  functor (X : Tagged) ->
    sig
      type t = X.t
      val hash : t -> int
      val equal : t -> t -> bool
      val compare : t -> t -> int
    end

(** Convenience functor that creates [OrderedHash], [Map], [Set], and [Hashtbl] at once. *)
module StructMake : functor (X:Tagged) ->
  sig
    module T : OrderedHash with type t=X.t
    module M : Map.S with type key = T.t
    module S : Set.S with type elt=T.t
    module H : Hashtbl.S with type key = T.t
  end

module Mint : Map.S with type key = int
module Sint : Set.S with type elt = int
module Hint : Hashtbl.S with type key = int

(** Returns a unique (in a program execution) [int]. *)
val unique_int : unit -> int

(** Same as [List.list_for_all2], but returns [false] if lists have different lengths. *)
val list_eq_for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

(**  [smart_map f l] returns the same result as [map f l], but
     ensures that sharing is preserved. For example,
     [smart_map (fun x -> x) l == l] *)
val smart_map : ('a -> 'a) -> 'a list -> 'a list

(** [drop k l] drop first [k] elements of [l]. If [l] is
     shorter than [k], the empty list is returned. *)
val drop : int -> 'a list -> 'a list

(** [take k l] takes the first [k] elements of [l]. If [l]
    is shorter than [k], then fewer elements are returned.  *)
val take : int -> 'a list -> 'a list

(** [split_n k l] return rhd, a, tl such that 
    l = List.rev_append rhd (a::tl) and List.length rhd = k *)
val split_n : int -> 'a list -> 'a list * 'a * 'a list

(** [cut_n k l] return rhd, tl such that 
    l = List.rev_append rhd tl and List.length rhd = k *)
val cut_n : int -> 'a list -> 'a list * 'a list

(** [list_from_to i j] returns the list with all natural
     numbers from [i] to [j-1]. *)
val list_from_to : int -> int -> int list

(** [x |> f] is equivalent to [f x]. *)
val (|>) : 'a -> ('a -> 'b) -> 'b

(** [exc_to_opt f] returns [None] if [f ()] raises an
    exception and [Some (f ())] otherwise. *)
val exc_to_opt : (unit -> 'a) -> 'a option

(** [map_opt f o] returns [None] if [o] is [None] and
    applies [f] to the value contained in [o] otherwise *)
val map_opt : ('a -> 'b) -> 'a option -> 'b option

(** [format_to_string f] executes [f ()] and returns the resulting string. *)
val format_to_string : (Format.formatter -> unit) -> string

(** [fsprintf f] executes the format function with the standard
    string formatter. *)
val fsprintf : ('a, Format.formatter, unit) format -> 'a

(** [fsget a] ignores its argument and extracts the string
    from the standard string formatter. It is usually used
    as in [fsprintf .. |> fsget] *)
val fsget : unit -> string

val replicate_r : 'a list -> int -> 'a -> 'a list
val replicate   : int -> 'a -> 'a list

(* TODO remove this *)
val massoc : 'k -> ('k * 'v) list -> 'v option

val swap : 'a * 'b -> 'b * 'a

(** [compare_on f x y] yields the comparison
    [compare (f x) (f y)] *)
val compare_on : ('a -> 'b) -> 'a -> 'a -> int

(** [pplist sep pp_elt f l] takes a formatter [f], a separator
    [sep], and a pretty printer for ['e] and returns a
    pretty printer for lists of elements from ['e] *)
val pp_list : ('a, 'b, 'c, 'd, 'd, 'a) format6 ->
  (Format.formatter -> 'e -> unit) -> Format.formatter -> 'e list -> unit

(** [pplist_c] is equivalent to [pp_list ","] *)
val pp_list_c : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

(** [pplist_s] pretty prints a list of strings *)
val pp_list_s : Format.formatter -> string list -> unit
