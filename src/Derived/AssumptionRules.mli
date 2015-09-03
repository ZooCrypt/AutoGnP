open Util
open CoreRules
open TheoryTypes

val t_assm_dec :
  ?i_assms:Util.Sstring.t ->
  theory_state ->
  bool ->
  string option ->
  direction option ->
  ((int * int) list) option ->
  (string list) option ->
  tactic

val t_assm_comp :
  ?icases:Expr.Se.t ->
  theory_state ->
  bool ->
  string option ->
  ((int * int) list) option ->
  tactic
