
(*i*)
open Abbrevs
open Util
open Game
open Assumption
open Expr
open ExprUtils
(*i*)

(** A probability tag associates a real number in [0,1] to a
    security experiment. The three tags are interpreted as follows
    for some $G : E$:
    \begin{itemize}
    \item [Pr_Succ] stands for $Pr[ G : E ]$
    \item [Pr_Adv] stands for $2 * Pr[ G : E ] - 1$
    \item [Pr_Dist(G',E')] stands for $|Pr[ G:E ] - Pr[ G':E']|$
    \end{itemize}
*)
type pr_tag =
  | Pr_Succ
  | Pr_Adv
  | Pr_Dist of sec_exp

let pr_exp_equal pre1 pre2 =
  match pre1, pre2 with
  | Pr_Adv,Pr_Adv | Pr_Succ,Pr_Succ -> true
  | Pr_Dist(se1),Pr_Dist(se2) -> se_equal se1 se2
  | _ -> false

(** The judgment [(G:Ev, pt)] is valid if the corresponding
    probability (see above) is negligible. A proof additionally
    establishes a concrete relation between judgments. *)
type judgment = { ju_se : sec_exp; ju_pr : pr_tag }

let ju_equal ju1 ju2 =
  se_equal ju1.ju_se ju2.ju_se && pr_exp_equal ju1.ju_pr ju2.ju_pr

let pp_ju fmt ju =
  match ju.ju_pr with
  | Pr_Succ -> 
    F.fprintf fmt "Pr[ G : E ] negligible where@\nG : E := @\n@[<hv 2>  %a@\n  : %a@]"
      (pp_gdef ~nonum:false) ju.ju_se.se_gdef pp_exp ju.ju_se.se_ev
  | Pr_Adv -> 
    F.fprintf fmt
      "2*Pr[ G : E ] - 1 negligible where@\nG : E := @\n@[<hv 2>  %a@\n  : %a@]"
      (pp_gdef ~nonum:false) ju.ju_se.se_gdef pp_exp ju.ju_se.se_ev
  | Pr_Dist se -> 
    F.fprintf fmt
      ("| Pr[ G : E ] - Pr[ G' : E' ] | negligible where@\n"^^
       "G : E := @\n@[<hv 2>  %a@\n  : %a@]@\n"^^
       "and G' : E' := @\n@[<hv 2>  %a@\n  : %a@]")
      (pp_gdef ~nonum:false) ju.ju_se.se_gdef pp_exp ju.ju_se.se_ev
      (pp_gdef ~nonum:false) se.se_gdef pp_exp se.se_ev

(* \hd{Low-level rules (extractable to EasyCrypt).} *)

type rule_name =

  (* \hd{Equivalence/small statistical distance: main} *)

  (* Rename, unfold let, and normalize. *)
  | Rconv 

  (* $Rswap(p,i)$: swap statement at $p$ forward by $i$. *)
  | Rswap   of gcmd_pos * int
  
  (* $Rnd(p,c_1,c_2,v)$: Perform optimistic sampling with
     bijection $c_1=c_2^{-1}$ for $v$ at position $p$. *)
  | Rrnd    of gcmd_pos * vs  * ctxt * ctxt

  (* $Rexc(p,\vec{e})$: change sampling at $p$ to exclude expressions $\vec{e}$. *)
  | Rexc of gcmd_pos * expr list


  (* \hd{Equivalence/small statistical distance: oracle} *)

  (* $Rrw\_orcl(p,dir)$: rewrite oracle with equality test at $p$ in $dir$. *)
  | Rrw_orcl   of ocmd_pos * direction

  (* $Rswap\_orcl(op,i)$: swap statement at $p$ forward by $i$. *)  
  | Rswap_orcl of ocmd_pos * int

  (* $Rnd\_orcl(p,c_1,c_2,v)$: rnd with $c_1=c_2^{-1}$ for $v$ at $p$. *)
  | Rrnd_orcl  of ocmd_pos * ctxt * ctxt

  (* $Rexc\_orcl(p,\vec{e})$: change sampling at $p$ to exclude $\vec{e}$. *)
  | Rexc_orcl  of ocmd_pos * expr list


  (* \hd{Case distinctions, up-to} *)

  (* $Rcase(e)$: refine event by performing case distinction on $e$. *)
  | Rcase_ev  of bool * expr

  (* $Radd\_test(p,e,a,\vec{v})$: add test $e$ at position $p$ to oracle,
     adversary $a$ and $\vec{v}$ used for bounding bad. *)
  | Radd_test of ocmd_pos * expr * ads * vs list

  (* $Rbad(p,v)$: Replace hash call at position $p$ by random variable $v$. *)
  | Rbad      of gcmd_pos * vs

  (* \hd{Implication rules for events} *)

  (* $Rctxt\_ev(i,c)$: apply context $c$ to $i$-th conjunct in event. *)
  | Rctxt_ev   of int * ctxt

  (* $Rremove\_ev(\vec{i})$: Remove given conjuncts. *)
  | Rremove_ev of int list

  (* $Rmerge\_ev(i,j)$: Merge given conjuncts as equality on tuples. *)
  | Rmerge_ev  of int * int

  (* $Rsplit\_ev(i)$: Split $i$-th event into separate equalities
     if it an equality on a tuple type. *)
  | Rsplit_ev  of int

  (* $Rrw\_ev(i,d)$: Rewrite event using $i$-th conjunct in direction $d$.
     If the conjunct is an inequality [a <> b], rewrite witb [(a=b) = false]. *)
  | Rrw_ev     of int * direction

  (* $Rassert(e)$: add assert(e) at position e after proving that G : ev /\ not
                   e negl. Requires that evaluating e is stable after position p. *)
  | Rassert of gcmd_pos * expr

  (* \hd{Apply assumption} *)

  | Rassm_dec  of (int * int) list * direction * renaming * assm_dec
  | Rassm_comp of (int * int) list * renaming * assm_comp

  (* \hd{Terminal rules} *)
  | Radmit of string

  | Rfalse_ev

  | Rrnd_indep of bool * int

  | Rdist_sym

  | Rdist_eq

  | Rtrans  (* FIXME: do we need any arguments? *)

  | Rhybrid (* FIXME: add arguments *)

  | Rswap_main of ocmd_pos_eq
