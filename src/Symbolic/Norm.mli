(** Compute the normal-form of expressions. *)
open Type
open Expr

val base_projs : ty -> (ty * ty * ty) list
  (** Return the list of projections (skip, take, remainder
      that split the given type into its base-type sized
      constituents. *)

val split_basic_type : expr -> expr list
  (** Split the given [expr] into its base-type sized constituents. *)

val xor_to_list : 'a gexpr -> 'a gexpr list
  (** Flatten an xor-term and return the maximal non-xor subterms. *)

val list_to_xor : expr list -> ty -> expr
  (** Smart constructor for [Xor]. *)

val se_of_list : expr list -> Se.t
  (** Convert [expr list] to corresponding expression set. *)

val xor_to_set : expr -> Se.t
  (** Defined such that [xor_to_set e = se_of_list (xor_to_list e)]. *)

val norm : expr -> expr
  (** Compute the normal form of the given expression. *)