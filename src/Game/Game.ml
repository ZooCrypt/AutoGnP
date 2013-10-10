(* Representing Games *)

(* (excepted) distributions for sampling *)
type distr = Type.ty * Expr.expr list (* uniform distribution over type t except for given values *)

(* list monad command for oracle definition *)
type lcmd = LLet   of (Vsym.t list * Expr.expr) (* LLet(x,e): let (x1,..,xk) = e *)
          | LBind  of (Vsym.t list * Hsym.t)    (* LBind([x1;..;xk], h): (x1,..,xk) <- L_h *)
          | LSamp  of (Vsym.t * distr)          (* LSamp(x,d): x <-$ d *)
          | LGuard of Expr.expr                 (* LGuard(t): t *)

(* oracle definition *)
type odef = Osym.t * Vsym.t list * lcmd list * Expr.expr
  (* (o,[x1;..;xl], [m1;..;mk],e): o(x1,..,xl) = [e | m1, .., mk] *)

(* game command *)
type gcmd = GLet  of (Vsym.t list * Expr.expr) (* GLet([x1;..xk], e): let (x1,..,xk) = e *)
          | GSamp of (Vsym.t * distr)          (* GSamp(x,d): x <-$ d *)
          | GCall of (Vsym.t list * Expr.expr list * odef list)

(* game definition *)
type gdef = gcmd list

let wf_odef od = true

let wf_gdef gd = true