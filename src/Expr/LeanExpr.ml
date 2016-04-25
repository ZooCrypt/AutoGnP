open Syms
open Expr
       
module L = Lean

let _TODO _ = failwith "Not implemented"
             
module ImportLeanDefs (LF : L.LeanFiles) = struct
  include L.GetExprParser(LF)                                             
  let mk_Eq   = get "eq"        |> as_2ary
  let mk_GExp = get "expr.Exp"  |> as_2ary
  let mk_GGen = get "expr.Ggen"
  let mk_Z    = _TODO
  let mk_B =
    let ltrue,lfalse = (get "true", get "false") in
    fun b -> if b then ltrue else lfalse
  let mk_FNat : int -> t =
    let nat_zero = get "nat.zero" in
    let nat_succ = get "nat.succ" |> as_1ary in
    let neg_succ_of_nat = get "neg_succ_of_nat" |> as_1ary in
    let rec lint_of_int = function
      | 0 -> nat_zero
      | n when n < 0 -> neg_succ_of_nat @@ lint_of_int (-n - 1)
      | n -> nat_succ @@ lint_of_int (n-1) in
    let t_of_lint = get "expr.Fint" |> as_1ary in
    fun n -> t_of_lint @@ lint_of_int n                                    
  let mk_FPlus = get "expr.Fop2 expr.fop2.Fadd" |> as_2ary

  let lean_eq e1 ?(ty = get_type e1) e2 =
    let eq = get "@eq.{1}" |> as_nary in
    eq [ty; e1; e2]
  let (|=|) = lean_eq
end
(* Now that the functor is defined,
the module only needs to be instanciated with a call to the functor,
e.g., *)

module LeanEnv =
  ImportLeanDefs(
      struct
        let _olean = ["data/nat"]
        let _lean = ["../autognp-lean/expr.lean"]
                      (* TODO : should be read from commandline *)
      end)
module LE = LeanEnv
              
type lean_expr = LeanEnv.t

let mk_Const = function
  | GGen -> LE.mk_GGen
  | FNat i -> LE.mk_FNat i
  | Z -> _TODO ()
  | B b -> LE.mk_B b

let lean_expr_of_expr_node_leaf = function
  | V vs -> L.Expr.mk_const @@ VarSym.to_string vs
  | Cnst c -> mk_Const c
  | _ -> invalid_arg "e_node leaf (V _ | Cnst _) expected"

module LeanExprOfExpr =
  Expr.OfExpr
    (struct
      type t = lean_expr
      let of_expr_node_leaf = lean_expr_of_expr_node_leaf
      let of_op : Expr.op -> t list -> t = _TODO
    end)
    
let lean_expr_of_expr = LeanExprOfExpr.f
                          
