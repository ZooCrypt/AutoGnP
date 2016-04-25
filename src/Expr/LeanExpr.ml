module L = Lean

module ImportLeanDefs (LF : L.LeanFiles) = struct
  include L.GetExprParser(LF)                                             
  let mk_Eq   = get "eq"        |> as_2ary
  let mk_GExp = get "expr.Exp"  |> as_2ary
  let mk_GGen = get "expr.Ggen"
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
      end)

type lean_expr = LeanEnv.t

let lean_expr_of_expr = failwith "TODO"
