module Ht = Hashtbl
module T = Type
module G = Game

type proofstate =
  { ps_lvars   : (string, T.Lenvar.id) Ht.t; 
    ps_gvars   : (string, T.Groupvar.id) Ht.t; 
    ps_rodecls : (string, Hsym.t) Ht.t;
    ps_odecls  : (string, Osym.t) Ht.t;
    ps_adecls  : (string, Asym.t) Ht.t;
    ps_emdecls : (string, Esym.t) Ht.t;
    ps_assms   : (string, Assumption.assumption_decision) Ht.t;
    ps_vars    : (string, Vsym.t) Ht.t;
    ps_goals   : (G.judgment list) option
  }

let mk_ps () =
  { ps_lvars   = Ht.create 20;
    ps_gvars   = Ht.create 20;
    ps_rodecls = Ht.create 20;
    ps_odecls  = Ht.create 20; 
    ps_adecls  = Ht.create 20;
    ps_emdecls = Ht.create 20;
    ps_assms   = Ht.create 5;
    ps_vars    = Ht.create 20; 
    ps_goals   = None }

let ps_copy ps =
  { ps with
    ps_lvars   = Ht.copy ps.ps_lvars;
    ps_gvars   = Ht.copy ps.ps_gvars;
    ps_rodecls = Ht.copy ps.ps_rodecls;
    ps_odecls  = Ht.copy ps.ps_odecls; 
    ps_adecls  = Ht.copy ps.ps_adecls;
    ps_emdecls = Ht.copy ps.ps_emdecls;
    ps_assms   = Ht.copy ps.ps_assms;
    ps_vars    = Ht.create 20;
  }

let ps_resetvars ps =
  { ps with
    ps_vars    = Ht.create 20;
    ps_goals   = None }

let create_lenvar ps s =
  try Ht.find ps.ps_lvars s 
  with Not_found ->
    let lv = T.Lenvar.mk s in
    Ht.add ps.ps_lvars s lv;
    lv

let create_groupvar ps s =
  try Ht.find ps.ps_gvars s 
  with Not_found ->
    let gv = T.Groupvar.mk s in
    Ht.add ps.ps_gvars s gv;
    gv

let create_var reuse ps s ty =
  if Ht.mem ps.ps_vars s then (
    if reuse then Some (Ht.find ps.ps_vars s)
    else None
  ) else (
    let v = Vsym.mk s ty in
    Ht.add ps.ps_vars s v;
    Some v
  )

let create_var_reuse ps s ty =
  if Ht.mem ps.ps_vars s then (
    Ht.find ps.ps_vars s
  ) else (
    let v = Vsym.mk s ty in
    Ht.add ps.ps_vars s v;
    v
  )


