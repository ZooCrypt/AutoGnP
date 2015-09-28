(* * Guard rules (Guess) *)

open Syms
open Tactic

val t_guess_maybe :
   Asym.t option -> Game.vs list option -> tactic
