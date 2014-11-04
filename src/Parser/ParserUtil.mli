(*s Types and conversion functions for parsed types, expressions, games, proof scripts, and tactics. *)

(*i*)
open TheoryState
open Expr
open Type
open Game
open Syms
open Gsyms
(*i*)

exception ParseError of string

val fail_parse : string -> 'a

val create_var : vmap -> string -> ty -> Vsym.t

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

val ty_of_parse_ty : theory_state -> parse_ty -> ty

val mk_Tuple : expr list -> expr

val bind_of_parse_bind :
  vmap -> theory_state -> (string * string) list -> (Vsym.t * Hsym.t) list

val expr_of_parse_expr : vmap -> theory_state -> parse_expr -> expr

val lcmd_of_parse_lcmd : vmap -> theory_state -> lcmd -> Game.lcmd

val odef_of_parse_odef :
  vmap -> theory_state ->
  string * string list * (lcmd list * parse_expr) ->
  Osym.t * Vsym.t list * Game.lcmd list * expr

val gcmd_of_parse_gcmd : vmap -> theory_state -> gcmd -> Game.gcmd

val gdef_of_parse_gdef : vmap -> theory_state -> gcmd list -> Game.gcmd list

val ju_of_parse_ju : vmap -> theory_state -> gcmd list -> parse_expr -> judgment

type tactic =
  | Rnorm
  | Rsimp
  | Rfalse_ev
  | Rnorm_nounfold
  | Rnorm_unknown  of string list
  | Rnorm_solve    of parse_expr
  | Rswap          of int * int
  | Rswap_oracle   of ocmd_pos * int
  | Rctxt_ev       of string * parse_expr * int
  | Rrnd           of bool * int option * (string * parse_expr) option * (string * parse_expr) option
  | Rrnd_orcl      of ocmd_pos option * (string * parse_expr) option * (string * parse_expr) option
  | Requiv         of gdef * parse_expr
  | Rassm_dec      of bool * string option * Util.direction option * ((int * int) list) option * (string list) option
  | Rassm_comp     of bool * string option * ((int * int) list) option
  | Rlet_abstract  of int option * string * parse_expr option * int option
  | Rsubst         of int * parse_expr * parse_expr
  | Rlet_unfold    of int
  | Rindep         of bool
  | Rcrush         of bool * int option
  | Rbad           of int * string
  | Rexcept        of int option * (parse_expr list) option
  | Rexcept_orcl   of ocmd_pos * parse_expr list
  | Radd_test      of ocmd_pos option * parse_expr option * string option * (string list) option
  | Rrewrite_orcl  of ocmd_pos * Util.direction
  | Rcase_ev       of parse_expr option
  | Rremove_ev     of int list
  | Rrewrite_ev    of int * Util.direction
  | Rsplit_ev      of int
  | Deduce         of parse_expr list * parse_expr

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
  | Unsafe     of bool
  | Admit
  | Last
  | Back
  | UndoBack   of bool
  | Qed
  | Extract    of string
  | Debug      of string

type theory = instr list
