(*s Types for parser *)

(*i*)
open Game
open Assumption
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
  | InLog  of parse_expr * string 

type parse_ctx = string * parse_ty option * parse_expr

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

type range_pos = assgn_pos option * assgn_pos option

type range = int * int
type ranges = range_pos list

type tactic =
  | Rseq           of tactic list
  | Rnorm
  | Rdist_eq
  | Rdist_sym
  | Rfalse_ev
  | Rnorm_nounfold
  | Rrename        of string * string
  | Rsimp          of bool
  | Rnorm_unknown  of string list
  | Rnorm_solve    of parse_expr
  | Rswap          of range_pos * assgn_pos
  | Rswap_oracle   of ocmd_pos * int
  | Rswap_main     of ocmd_pos * string
  | Rctxt_ev       of int option * parse_ctx option
  | Rrnd           of bool * assgn_pos option * parse_ctx option *
                      parse_ctx option * parse_expr option
  | Rrnd_orcl      of ocmd_pos option * parse_ctx option * parse_ctx option
  | Rconv          of gdef * parse_expr
  | Rtrans         of gdef * parse_expr
  | Rassm_dec      of bool * string option * direction option * ranges *
                      (string list) option
  | Rassm_comp     of bool * string option * ranges
  | Rlet_abstract  of assgn_pos option * string * parse_expr option * 
                      assgn_pos option * bool
  | Rsubst         of assgn_pos option * parse_expr * parse_expr * 
                      assgn_pos option
  | Rlet_unfold    of assgn_pos list
  | Rindep         of bool
  | Rcrush         of bool * int option
  | Rbad           of int * string
  | Rexcept        of assgn_pos option * (parse_expr list) option 
  | Rexcept_orcl   of ocmd_pos * parse_expr list
  | Radd_test      of ocmd_pos option * parse_expr option * string option *
                      (string list) option
  | Rhybrid        of (int * int) * lcomp * string
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
  | AssmComp   of string * assm_type * gdef * parse_expr * string list list
  | JudgSucc   of gdef * parse_expr 
  | JudgAdv    of gdef * parse_expr
  | JudgDist   of gdef * parse_expr * gdef * parse_expr
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
  | PrintGame  of string
  | PrintGames of string * string

type theory = instr list
