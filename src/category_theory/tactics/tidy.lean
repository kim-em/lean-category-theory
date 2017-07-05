-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .congr_fun_assumptions .fsplit .simp_hypotheses .dsimp_hypotheses .automatic_induction .unfold_projections .nat_inequality
import .chain
import .smt

open tactic


private meta def dsimp_eq_mpr : tactic unit := `[dsimp [eq.mpr]]

meta def tidy_tactics : list (tactic string) :=
[
  tactic.triv                   >> pure "triv", 
  force (reflexivity)           >> pure "refl", 
  nat_inequality                >> pure "nat_inequality" ,
  applicable                    >> pure "applicable" ,
  force (intros >> skip)        >> pure "intros" ,
  force (fsplit)                >> pure "fsplit" ,
  force (dsimp_eq_mpr)          >> pure "dsimp [eq.mpr]" ,
  unfold_projections            >> pure "unfold_projections" ,
  simp                          >> pure "simp" ,
  dsimp_hypotheses              >> pure "dsimp_hypotheses" ,
  automatic_induction           >> pure "automatic_induction" ,
  unfold_projections_hypotheses >> pure "unfold_projections_hypotheses" ,
  simp_hypotheses               >> pure "simp_hypotheses",
  tactic.interactive.congr_fun_assumptions
]

meta def tidy ( max_steps : nat := chain_default_max_steps ) ( trace_progress : bool := ff ) : tactic unit :=
do results ← chain tidy_tactics max_steps,
   if trace_progress then
     trace ("... chain tactic used: " ++ results.to_string)
   else
     skip

meta def blast ( max_steps : nat := chain_default_max_steps ) ( trace_progress : bool := ff ) : tactic unit := 
do results ← chain (tidy_tactics ++ [ any_goals ( smt_eblast >> done ) >> pure "smt_eblast" ]) max_steps,
   if trace_progress then
     trace ("... chain tactic used: " ++ results.to_string)
   else
     skip

notation `♮` := by abstract { smt_eblast }
notation `♯` := by abstract { blast }