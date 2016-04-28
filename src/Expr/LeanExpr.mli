type lean_expr
               
val of_expr : Expr.expr -> lean_expr

module LEnv : sig
  (* Public Lean Environment Utilities *)  
  type t = lean_expr
  val to_string : t -> string
  val to_pp_string : t -> string
  val get_type : t -> t
  val get     : string -> t
  (*  val get_with_univ_params : string -> t * list_name                            *)
  val as_1ary : t -> t -> t
  val as_2ary : t -> t -> t -> t
  val as_nary : t -> t list -> t
  val (<@) : t -> t -> t (* Syntactic sugar for "Lean argument feeding" *)
                       
  (* Proof obligation generation *)                  
  val add_proof_obligation :
    ?prefix:string -> ?name:string -> t -> unit
  val proof_obligations_to_string : unit -> string
  val export_proof_obligations : string -> unit
end
                
