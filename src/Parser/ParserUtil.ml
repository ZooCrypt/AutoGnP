(** Types for parsing: Expressions, scheme descriptions, and commands. *)


type parse_expr =
  | V     of string
  | H     of string * parse_expr
  | Tuple of parse_expr list
  | Proj  of int * parse_expr
  | Cnst  of cnst
  | App   of op * parse_expr list
  | Nary  of naryop * parse_expr list
  | ElemH of parse_expr * string

(** Representation of input types. *)
type ity = string list

(** Representation of input expressions. *)
type iexpr =
  | IZ    of ity
  | IMsg 
  | IStar
  | IR    of string
  | IFun  of string * iexpr
  | IPinv of string * iexpr
  | IApp  of iexpr list
  | IProj of (ity * ity) * iexpr
  | IXor  of iexpr * iexpr

type rvar = string
type hsym = string
type psym = string
type context = iexpr

(** Scheme description. *)
type descr =
  Descr of ity *                      (* msg type *)
           (hsym * ity * ity) list *  (* hash function symbols *)
           (psym * ity) list *        (* permutation function symbols *)
           (rvar * ity) list *        (* random variable symbols *)
           iexpr                      (* cipher *)

type cloc = LAdmit of int | LPath of int list

(** Proof command. *)
type cmd =
  | CNorm
  | CConj  of int
  | COpt   of rvar * iexpr
  | CPerm  of rvar * psym
  | CSplit of rvar * ity * rvar *  rvar
  | CMerge of rvar * rvar * rvar
  | CFail1 of hsym * rvar
  | CFail2 of hsym * rvar
  | CInd
  | CRnd   of rvar * context
  | COw    of psym * rvar * ity * ity * rvar list * context * context
  | CAdmit