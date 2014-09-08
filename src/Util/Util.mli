(*s This module defines types tagged with [int]s, some convenience functor
    applications for maps, sets, hashtables, and some convenience functions
    for lists and pretty printing. *)

(* \subsection{Convenience Functors} *)

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

module L : module type of List
module F : module type of Format

module Mint : Map.S with type key = int
module Sint : Set.S with type elt = int
module Hint : Hashtbl.S with type key = int

module Sstring : Set.S with type elt = string
module Mstring : Map.S with type key = string

(* \subsection{Misc functions} *)

(** Returns a unique (in a program execution) [int]. *)
val unique_int : unit -> int

(** [exc_to_opt f] returns [None] if [f ()] raises an
    exception and [Some (f ())] otherwise. *)
val exc_to_opt : (unit -> 'a) -> 'a option

(** [map_opt f o] returns [None] if [o] is [None] and
    applies [f] to the value contained in [o] otherwise *)
val map_opt : ('a -> 'b) -> 'a option -> 'b option

val from_opt : 'a -> 'a option -> 'a

val opt : ('a -> 'b) -> 'b -> 'a option -> 'b

val swap : 'a * 'b -> 'b * 'a

val map_accum : ('b -> 'a -> 'b * 'c) -> 'b -> 'a list -> 'b * 'c list

(** [compare_on f x y] yields the comparison [compare (f x) (f y)] *)
val compare_on : ('a -> 'b) -> 'a -> 'a -> int

val input_file : string -> string

val output_file : string -> string -> unit

val assert_msg : bool -> string -> unit

type ('a,'b) either = Left of 'a | Right of 'b

type direction = LeftToRight | RightToLeft

val string_of_dir : direction -> string

val id : 'a -> 'a

(* \subsection{List functions} *)

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

(** [split_n k l] return [rhd], [a], [tl] such that 
    [l = List.rev\_append rhd (a::tl)] and [List.length rhd = k] *)
val split_n : int -> 'a list -> 'a list * 'a * 'a list

(** [cut_n k l] returns rhd, tl such that 
    [l = List.rev_append rhd tl] and [List.length rhd = k] *)
val cut_n : int -> 'a list -> 'a list * 'a list

(** [filter_map f l] returns the list corresponding to apply [f] to each 
   elements of [l] and keep the one returning [Some] *)
val filter_map : ('a -> 'b option) -> 'a list -> 'b list

(** [list_from_to i j] returns the list with all natural
     numbers from [i] to [j-1]. *)
val list_from_to : int -> int -> int list

val replicate_r : 'a list -> int -> 'a -> 'a list

val replicate   : int -> 'a -> 'a list

val lefts : (('a,'b) either) list -> 'a list

val rights : (('a,'b) either) list -> 'b list

val lefts_rights : (('a,'b) either) list -> ('a list * 'b list)

val cat_Some : 'a option list -> 'a list

val conc_map : ('a -> 'b list) -> 'a list -> 'b list

(* \subsection{String functions} *)

val splitn : string -> char -> string list

val splitn_by : string -> (string -> int -> bool) -> string list

val string_find_from : string -> string -> int -> int option

val string_rfind_from : string -> string -> int -> int option

val split : string -> char -> (string * string) option

(* \subsection{Pretty printing} *)

(** [pplist sep pp_elt f l] takes a formatter [f], a separator
    [sep], and a pretty printer for ['e] and returns a
    pretty printer for lists of elements from ['e] *)
val pp_list : ('a, 'b, 'c, 'd, 'd, 'a) format6 ->
  (F.formatter -> 'e -> unit) -> F.formatter -> 'e list -> unit

(** [pplist_c] is equivalent to [pp_list ","] *)
val pp_list_c : (F.formatter -> 'a -> unit) -> F.formatter -> 'a list -> unit

(** [pplist_s] pretty prints a list of strings *)
val pp_list_s : F.formatter -> string list -> unit

val pp_string : F.formatter -> string -> unit

val pp_int : F.formatter -> int -> unit

val pp_if : bool -> ('a -> 'b -> 'c) -> ('a -> 'b -> 'c) -> 'a -> 'b -> 'c

val pp_pair : (F.formatter -> 'a -> unit) -> (F.formatter -> 'b -> unit) -> F.formatter -> 'a * 'b -> unit

(** [fsprintf f] executes the format function with the standard
    string formatter. *)
val fsprintf : ('a, F.formatter, unit, string) format4 -> 'a


(* \subsection{Exception required by Logic modules} *)

exception Invalid_rule of string 

(** [tacerror s] raises a rule application error with information [s]. *)
val tacerror : ('a, F.formatter, unit, 'b) format4 -> 'a

(* \subsection{Debug printing} *)

val eprintf : ('a, F.formatter, unit) format -> 'a

val set_debug_buffer : unit -> Buffer.t

