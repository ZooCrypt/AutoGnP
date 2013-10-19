open Game
open Expr
open Wf

type assumption_decision =
  { ad_prefix1 : gdef;
    ad_prefix2 : gdef;
    ad_privvars : Vsym.S.t; }

let mk_ad pref1 pref2 pvars =
  let check_nocall gd =
    List.for_all
      (function GLet _ -> true | GSamp _ -> true | _ -> false)
      gd
  in
  let pvarse =
    Vsym.S.fold (fun x acc -> Se.add (mk_V x) acc)
      pvars Se.empty
  in
  (* FIXME: check that groupvars(pref1) = groupvars(pref2) *)
  assert (check_nocall pref1);
  assert (check_nocall pref2);
  assert (ignore (wf_gdef pref1); true);
  assert (ignore (wf_gdef pref2); true);
  assert (Se.equal
           (Se.diff (gdef_vars pref1) pvarse)
           (Se.diff (gdef_vars pref1) pvarse));
  { ad_prefix1 = pref1;
    ad_prefix2 = pref2;
    ad_privvars = pvars }