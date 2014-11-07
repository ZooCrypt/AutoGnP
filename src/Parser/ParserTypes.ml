(*s Types for parser *)

(*i*)
open Game
open Util
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Types for parsed types, expressions, and games} *)

type parse_ty =
  | BS of string
  | Bool
  | G of string
  | Fq
  | Prod of parse_ty list

type parse_expr =
    V of string
  | SApp of string * parse_expr list
  | HApp of string * parse_expr list
  | Tuple of parse_expr list
  | Proj of int * parse_expr
  | CB of bool
  | CZ of string
  | CGen of string
  | CFNat of int
  | Mult of parse_expr * parse_expr
  | Plus of parse_expr * parse_expr
  | Exp of parse_expr * parse_expr
  | Log of parse_expr
  | Opp of parse_expr
  | Minus of parse_expr * parse_expr
  | Inv of parse_expr
  | Div of parse_expr * parse_expr
  | Eq of parse_expr * parse_expr
  | Not of parse_expr
  | Ifte of parse_expr * parse_expr * parse_expr
  | Land of parse_expr * parse_expr
  | Xor of parse_expr * parse_expr
  | Exists of parse_expr * parse_expr * (string * string) list

type parse_ctx = string * parse_expr

type lcmd =
    LLet of string * parse_expr
  | LBind of string list * string
  | LSamp of string * parse_ty * parse_expr list
  | LGuard of parse_expr

type lcomp = lcmd list * parse_expr

type odef = string * string list * lcomp

type gcmd =
    GLet of string * parse_expr
  | GSamp of string * parse_ty * parse_expr list
  | GCall of string list * string * parse_expr * odef list

type gdef = gcmd list

(*i ----------------------------------------------------------------------- i*)
(* \hd{Types for parsed proof scripts and tactics} *)

type assgn_pos =
  | Pos of int
  | Var of string

type tactic =
  | Rnorm
  | Rfalse_ev
  | Rnorm_nounfold
  | Rsimp          of bool
  | Rnorm_unknown  of string list
  | Rnorm_solve    of parse_expr
  | Rswap          of int * int
  | Rswap_oracle   of ocmd_pos * int
  | Rctxt_ev       of int option * (string * parse_expr) option
  | Rrnd           of bool * assgn_pos option * (string * parse_expr) option *
                      (string * parse_expr) option * parse_expr option
  | Rrnd_orcl      of ocmd_pos option * (string * parse_expr) option * (string * parse_expr) option
  | Requiv         of gdef * parse_expr
  | Rassm_dec      of bool * string option * direction option * ((int * int) list) option *
                      (string list) option
  | Rassm_comp     of bool * string option * ((int * int) list) option
  | Rlet_abstract  of int option * string * parse_expr option * int option * bool
  | Rsubst         of int * parse_expr * parse_expr * int option
  | Rlet_unfold    of assgn_pos option
  | Rindep         of bool
  | Rcrush         of bool * int option
  | Rbad           of int * string
  | Rexcept        of assgn_pos option * (parse_expr list) option
  | Rexcept_orcl   of ocmd_pos * parse_expr list
  | Radd_test      of ocmd_pos option * parse_expr option * string option * (string list) option
  | Rrewrite_orcl  of ocmd_pos * direction
  | Rcase_ev       of parse_expr option
  | Rremove_ev     of int list
  | Rrewrite_ev    of int * direction
  | Rsplit_ev      of int
  | Deduce         of parse_expr list * parse_expr
  | FieldExprs     of parse_expr list

type instr =
  | RODecl     of string * bool * parse_ty * parse_ty
  | EMDecl     of string * string * string * string
  | ODecl      of string * parse_ty * parse_ty
  | ADecl      of string * parse_ty * parse_ty
  | AssmDec    of string * gdef * gdef * (string list) list
  | AssmComp   of string * gdef * parse_expr * string list list
  | Judgment   of gdef * parse_expr
  | PrintGoal  of string
  | PrintGoals of string
  | PrintProof of bool
  | Apply      of tactic
  | Admit
  | Last
  | Back
  | UndoBack   of bool
  | Qed
  | Extract    of string
  | Debug      of string

type theory = instr list
