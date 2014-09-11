open Util
open CoreRules
open TheoryState

val t_assm_dec :
  ?i_assms:Util.Sstring.t ->
  theory_state ->
  bool ->
  string option ->
  direction option ->
  (string list) option ->
  tactic

val t_assm_comp :
  theory_state ->
  bool ->
  string option ->
  ParserUtil.parse_expr option ->
  tactic
