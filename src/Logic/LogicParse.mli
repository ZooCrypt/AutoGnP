(** Parse CPA scheme declaration *)
open ParserUtil
open Logic

(** {1 Typing environment } *)

exception TenvUndef of string * string

type sym = SRsym of Rsym.t | SPsym of Psym.t | SHsym of Hsym.t

(** Typing environment. Note that it is mutable *)
type tenv

val getTy : tenv -> ity -> Type.ty

val getRsym : tenv -> Logic.Mstring.key -> Rsym.t

val getHsym : tenv -> Logic.Mstring.key -> Hsym.t

val getPsym : tenv -> Logic.Mstring.key -> Psym.t

val te_of_cj : cpaJudgement -> tenv

(** {2 Scheme declaration and expression conversion} *)

val convert_expr : ?star:Type.ty -> tenv -> iexpr -> Expr.expr

exception CpaWrapError of (string * string)

val wrapError : (string ref -> 'a) -> 'a

val declare_scheme : string -> string -> string -> string -> string -> Logic.cpaProof