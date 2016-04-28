open Syms
module E = Expr       
module L = Lean

let _TODO _ = failwith "Not implemented (TODO)"
             
module ImportLeanDefs (LF : L.LeanFiles) = struct
  include L.GetExprParser(LF)
  (* Lean types *)
  let lty_bool = get "ty.Bl"
  let lty_G    = get "ty.Grp"
  let lty_Fq   = get "ty.Fq"
                     
  let as_lty ty =
    match ty.Type.ty_node with
    | Type.Bool -> lty_bool
    | Type.G _  -> lty_G
    | Type.Fq   -> lty_Fq
    | _    -> invalid_arg "Unsupported type" (* TODO : Add more type support ? *) 
  (* Groups *)
  let mk_GExp = get "expr.Exp"  |> as_2ary
  let mk_GGen = get "expr.Ggen"
  let mk_GLog = get "expr.Log" |> as_1ary
  let mk_GInv = get "expr.Ginv" |> as_1ary
  let mk_GMult = get "expr.Gmul" |> as_2ary
  (* Constants *)    
  let mk_V =
    let mk_var = get "var.Var" |> as_2ary
    and le_of_var = get "@expr.V" |> as_2ary in
    fun ~ty i ->
    let ty = as_lty ty in
    le_of_var ty @@ mk_var ty @@ lnat_of_posint i
    let mk_Z    = _TODO
  let mk_B =
    let ltrue,lfalse = (get "true", get "false") in
    fun b -> if b then ltrue else lfalse
  let mk_FNat n =
    get "expr.Fint" <@ lint_of_int n
    
  (* Field *)
  let mk_FPlus = get "expr.Fop2 E.expr.fop2.Fadd" |> as_2ary
  let mk_FOpp = get "expr.Fop1 fop1.Fop" |> as_1ary
  let mk_FMinus = get "expr.Fop2 fop2.Fsub" |> as_2ary
  let mk_FInv = get "expr.Fop1 fop1.Finv" |> as_1ary
  let mk_FMult = get "expr.Fop2 fop2.Fmul" |> as_2ary
  let mk_FDiv = get "expr.Fop2 fop2.Fdiv" |> as_2ary
  (* Tuple / Proj *)
  let mk_Tuple ?(ty = _TODO ()) =
    let nil = get "@list.nil.{1}" <@ ty in
    let (@:) = get "@list.cons.{1}" <@ ty |> as_2ary in
    let rec of_list = function
      | [] -> nil
      | x :: xs -> x @: of_list xs in
    of_list
  let mk_Proj _ = _TODO
  (* TODO : Defining a to_list function requires the type to be inhabited in Lean *)
  (* Equality *)                           
  let lean_eq e1 ?(ty = get_type e1) e2 =
    let eq = get "@eq.{1}" |> as_nary in
    eq [ty; e1; e2]
  let (|=|) = lean_eq
  let mk_Eq   = lean_eq
  (* Logic *)
  let mk_Not = get "not" |> as_1ary
  let mk_Land = get "and" |> as_2ary
  let mk_Lor = get "or" |> as_2ary                              
end

(* Now that the functor is defined,
the module only needs to be instanciated with a call to the functor,
e.g., *)

module LeanEnv =
  ImportLeanDefs(
      struct
        let _olean = ["data/nat"; "data/list"]
        let _lean = ["../autognp-lean/expr.lean"]
                      (* TODO : should be read from commandline *)
      end)
module LE = LeanEnv
              
type lean_expr = LeanEnv.t

let mk_Const = function
  | E.GGen -> LE.mk_GGen
  | E.FNat i -> LE.mk_FNat i
  | E.Z -> _TODO ()
  | E.B b -> LE.mk_B b
                   
(* Arity = 1 *)
let (!~) (go : E.expr -> lean_expr) (mk_lexpr : lean_expr -> lean_expr)
    : E.expr list -> lean_expr = function 
  | [e] -> mk_lexpr @@ go e
  | _ -> invalid_arg "expected list of length 1 for 1-ary function"
(* Arity = 2 *)
let (!~~) (go : E.expr -> lean_expr) (mk_lexpr : lean_expr -> lean_expr -> lean_expr)
    : E.expr list -> lean_expr = function 
  | [e1; e2] -> mk_lexpr (go e1) (go e2)
  | _ -> invalid_arg "expected list of length 2 for 2-ary function"
(* Any arity, thanks to associativity *)
let mk_Nary ~(go : E.expr -> lean_expr) assoc_op =
  let rec aux = function
  | [x] -> go x
  | [] -> invalid_arg "expected list of length >= 1 for n-ary function"
  | x::xs -> assoc_op (go x) (aux xs) in
  aux
    
let of_expr e =
  let rec go e = match e.E.e_node with
    | E.V vs ->
       LE.mk_V ~ty:e.E.e_ty (Id.tag vs.VarSym.id)
    | E.Cnst c ->
       mk_Const c
    | E.Tuple ((x::_) as es) ->
       let ty = LE.get_type @@ go x and les = List.map go es in
       LE.mk_Tuple ~ty les
    | E.Tuple _ ->
       failwith "TODO : Empty list implies undefined type"
    | E.Proj(i,e) ->
       LE.mk_Proj i (go e)
    | E.App(op, es) ->
       (match op with
        | E.GExp _ ->
           !~~ go LE.mk_GExp es
        | E.GLog _ ->
           !~ go LE.mk_GLog es
        | E.GInv   ->
           !~ go LE.mk_GInv es                         
        | E.FOpp   ->
           !~ go LE.mk_FOpp es
        | E.FMinus ->
           !~~ go LE.mk_FMinus es
        | E.FInv   ->
           !~ go LE.mk_FInv es
        | E.FDiv   ->
           !~~ go LE.mk_FDiv es
        | E.Eq -> let ty = LE.get_type @@ go @@ List.hd es in
           !~~ go (LE.mk_Eq ~ty) es
        | E.Not    ->
           !~ go LE.mk_Not es
        | _        -> _TODO ())
    | E.Nary (nop, es) -> let lean_assoc_op = match nop with
                            | E.GMult -> LE.mk_GMult
                            | E.FPlus -> LE.mk_FPlus
                            | E.FMult -> LE.mk_FMult
                            | E.Land  -> LE.mk_Land
                            | E.Lor   -> LE.mk_Lor
                            | E.Xor   -> _TODO () in
                          mk_Nary ~go lean_assoc_op es
    | E.Quant(E.All, binding, e)
      | E.Quant(_, binding, e) -> _TODO () in
  go e
     

                 
                          
