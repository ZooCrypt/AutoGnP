(*s Types for parser *)

(*i*)
open Game
open Syms
open Assumption
open Util
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Types for parsed types, expressions, and games} *)

type parse_ty =
  | KeyPair of string
  | PKey of string
  | SKey of string
  | BS of string
  | Bool
  | G of string
  | Fq
  | Prod of parse_ty list

let mk_Prod = function [t] -> t | ts -> Prod ts

type parse_expr =
  | V of string qual * string
  | SApp of string * parse_expr list
  | Tuple of parse_expr list
  | ParsePerm of string * bool * parse_expr * parse_expr
  | ParseGetPK of string * parse_expr
  | ParseGetSK of string * parse_expr
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
  | All of (string list * string) list *  parse_expr

let mk_Tuple = function [t] -> t | ts -> Tuple ts

type parse_ctx = string * parse_ty option * parse_expr

type lcmd =
    LLet of string * parse_expr
  | LBind of string list * string
(*  | LSampKP of string * parse_ty * parse_expr list *)
  | LSamp of string * parse_ty * parse_expr list
  | LGuard of parse_expr

type lcomp = lcmd list * parse_expr

type odec = Odef of lcomp | Ohybrid of (lcomp * lcomp * lcomp)

type odef = string * string list * odec

type gcmd =
    GLet    of string * parse_expr
  | GAssert of parse_expr
  | GSamp   of string * parse_ty * parse_expr list
  | GCall   of string list * string * parse_expr * odef list

type gdef = gcmd list

(*i ----------------------------------------------------------------------- i*)
(* \hd{Types for parsed proof scripts and tactics} *)

type assgn_pos =
  | Pos    of int
  | Var    of string
  | AbsPos of int

type diff_cmd =
  | Drename of string * string * assgn_pos option
  | Dinsert of assgn_pos * gcmd list
  | Dsubst  of assgn_pos * parse_expr * parse_expr

type selector = InRight | InBoth (* InLeft is default *)

type range_pos = assgn_pos option * assgn_pos option

type range = int * int
type ranges = range_pos list


type parse_ev = (Game.quant * (string list * string) list) * parse_expr

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
  | Rswap_to_main  of ocmd_pos_eq * string
  | Rswap_to_orcl  of assgn_pos * ocmd_pos_eq * string
  | Rctxt_ev       of int option * parse_ctx option
  | Rrnd           of bool * assgn_pos option * parse_ctx option *
                      parse_ctx option * parse_expr option
  | Rrnd_exp       of bool * (string * string option) list
  | Rrnd_orcl      of ocmd_pos option * parse_ctx option * parse_ctx option
  | Rconv          of gdef option * parse_ev
  | Rtrans         of gdef * parse_ev
  | Rtrans_diff    of diff_cmd list
  | Rassm_dec      of bool * string option * direction option * ranges *
                      (string list) option
  | Rassm_comp     of bool * string option * ranges
  | Rlet_abstract  of assgn_pos option * string * parse_expr option * 
                      assgn_pos option * bool
  | Rlet_abstract_deduce
    of bool * assgn_pos * string * parse_expr * assgn_pos option
  | Rassert        of assgn_pos * parse_expr option
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
  | Rhybrid        of (int * int) * lcomp
  | Rrewrite_orcl  of ocmd_pos * direction
  | Rcase_ev       of parse_expr option
  | Rremove_ev     of int list
  | Rrewrite_ev    of int * direction
  | Rsplit_ev      of int
  | Rsplit_ineq    of int
  | Deduce         of bool * parse_expr list * parse_expr
  | FieldExprs     of parse_expr list
  | Rguard         of ocmd_pos * parse_expr option
  | Rguess         of string * string list
  | Rfind          of (string list * parse_expr) * parse_expr * string * string list

type instr =
  | PermDecl   of string * parse_ty
  | RODecl     of string * bool * parse_ty * parse_ty
  | EMDecl     of string * string * string * string
  | ODecl      of string * parse_ty * parse_ty
  | ADecl      of string * parse_ty * parse_ty
  | AssmDec    of string * bool * gdef * gdef * (string list) list
  | AssmComp   of string * bool * assm_type * gdef * parse_ev * string list list
  | JudgSucc   of gdef * parse_ev 
  | JudgAdv    of gdef * parse_ev
  | JudgDist   of gdef * parse_ev * gdef * parse_ev
  | PrintGoal  of string
  | PrintGoals of string
  | PrintProof of bool * string option
  | Apply      of tactic
  | Admit
  | Last
  | Back
  | UndoBack   of bool
  | Qed
  | Restart
  | Extract    of string
  | Debug      of string
  | PrintGame  of string
  | PrintGames of string * string

type theory = instr list
