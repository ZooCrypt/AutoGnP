(*s Functions on expressions that do not require access to internals *)

(*i*)
open Abbrevs
open Syms
open Expr
open Type
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Indicator functions} *)

val is_V : expr -> bool
val is_H : expr -> bool
val is_Tuple : expr -> bool
val is_Proj : expr -> bool
val is_some_Cnst : expr -> bool
val is_Cnst : cnst -> expr -> bool
val is_FNat : expr -> bool
val is_FOne : expr -> bool
val is_FZ : expr -> bool
val is_True : expr -> bool
val is_False : expr -> bool
val is_GGen : expr -> bool
val is_GLog : expr -> bool
val is_GLog_gv : Groupvar.id -> expr -> bool
val is_some_App : expr -> bool
val is_App : op -> expr -> bool
val is_FDiv : expr -> bool
val is_FOpp : expr -> bool
val is_GExp : expr -> bool
val is_some_Nary : expr -> bool
val is_Nary : nop -> expr -> bool
val is_FPlus : expr -> bool
val is_FMult : expr -> bool
val is_Xor : expr -> bool  
val is_Exists : expr -> bool
val is_Eq    : expr -> bool
val is_Not : expr -> bool
val is_field_op : op -> bool
val is_field_nop : nop -> bool
val is_field_exp : expr -> bool
val is_Land : expr -> bool

(*i ----------------------------------------------------------------------- i*)
(* \hd{Destructor functions} *)

exception Destr_failure of string

val destr_V      : expr -> Vsym.t
val destr_H      : expr -> Hsym.t * expr
val destr_Tuple  : expr -> expr list
val destr_Proj   : expr -> int * expr
val destr_Cnst   : expr -> cnst
val destr_FNat   : expr -> int
val destr_App    : expr -> op * expr list
val destr_GMult  : expr -> (expr) list
val destr_GExp   : expr -> expr * expr
val destr_GLog   : expr -> expr
val destr_EMap   : expr -> Esym.t * expr * expr
val destr_FOpp   : expr -> expr
val destr_FMinus : expr -> expr * expr
val destr_FInv   : expr -> expr
val destr_FDiv   : expr -> expr * expr
val destr_Eq     : expr -> expr * expr
val destr_Not    : expr -> expr
val destr_Ifte   : expr -> expr * expr * expr
val destr_FPlus  : expr -> expr list
val destr_FMult  : expr -> expr list
val destr_Xor    : expr -> expr list
val destr_Land   : expr -> expr list
val destr_Exists  : expr -> expr * expr * (Vsym.t * Hsym.t) list
val destr_Xor_nofail : expr -> expr list
val destr_Land_nofail : expr -> expr list
val destr_Tuple_nofail : expr -> expr list

(*i ----------------------------------------------------------------------- i*)
(* \hd{Pretty printing} *)

val pp_cnst : F.formatter -> cnst -> Type.ty -> unit
val pp_exp  : F.formatter -> expr -> unit
val pp_op   : F.formatter -> op * expr list -> unit
val pp_nop  : F.formatter -> nop * expr list -> unit

val pp_exp_tnp  : F.formatter -> expr -> unit

(*i ----------------------------------------------------------------------- i*)
(* \hd{Useful functions on [expr]} *)

val e_iter_ty_maximal : ty -> (expr -> unit) -> expr -> unit

(** [e_vars e] returns the set of all variables in [e]. *)
val e_vars : expr -> Se.t

val has_log : expr -> bool

val is_ppt : expr -> bool

val se_of_list : expr list -> Se.t

val se_disjoint : Se.t -> Se.t -> bool

val me_of_list : (Me.key * 'a) list -> 'a Me.t

type ctxt = Vsym.t * expr

val inst_ctxt : ctxt -> expr -> expr

(** [sub t] is a generic subtraction function that
    returns context [(x1,x2,c)] and a [zero]
    such that forall e1 e2:t, [inst_ctxt c e1 e2] =E [e1 - e2]
    and [inst_ctxt c e2 e2] = [zero]. *)
val sub : ty -> (Vsym.t * ctxt) * expr

val is_Zero : expr -> bool

val mk_Zero   : ty -> expr

val typeError_to_string : ty * ty * expr * expr option * string -> string

val catch_TypeError : (unit -> 'a) -> 'a

type inverter = I of expr

val expr_of_inverter : inverter -> expr
