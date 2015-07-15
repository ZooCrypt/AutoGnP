(*s Well-formedness of games. *)

(*i*)
open Syms
open Expr
(*i*)

exception Wf_var_undef of Vsym.t * expr * Vsym.S.t

exception Wf_div_zero of Expr.expr list

type wf_check_type = CheckDivZero | NoCheckDivZero

type wf_state
 
val mk_wfs : unit -> wf_state

val ensure_name_fresh : wf_state -> Util.Sstring.elt -> wf_state

val ensure_names_fresh : wf_state -> Util.Sstring.elt list -> wf_state

val ensure_varname_fresh : wf_state -> Vsym.S.elt -> wf_state

val ensure_varnames_fresh : wf_state -> Vsym.S.elt list -> wf_state

val check_nonzero : wf_check_type -> wf_state -> Expr.expr -> bool

val wf_exp : wf_check_type -> wf_state -> Expr.expr -> unit

val wf_lcmds :
  wf_check_type -> wf_state -> (Vsym.S.t ref) option -> Game.lcmd list -> wf_state

val wf_odef : wf_check_type -> wf_state -> (Vsym.S.t ref) option-> Game.odef -> unit

val wf_gdef : wf_check_type -> Game.gcmd list -> wf_state

val wf_ev : wf_check_type -> wf_state -> Game.ev -> unit
val wf_se : wf_check_type -> Game.sec_exp -> unit
