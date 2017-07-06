-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .congr_fun_assumptions .fsplit .simp_hypotheses .dsimp_hypotheses .automatic_induction .unfold_projections
import .chain
import .smt

open tactic

private meta def dsimp_eq_mpr : tactic unit := `[dsimp [eq.mpr] {unfold_reducible := tt}]

meta def if_exactly_one_goal { α : Type } ( t : tactic α ) : tactic α :=
do ng ← num_goals,
   if ng = 1 then t else fail "there is not exactly one goal"

meta def tidy_tactics : list (tactic string) :=
[
  tactic.triv                   >> pure "triv", 
  force (reflexivity)           >> pure "refl", 
  if_exactly_one_goal assumption >> pure "assumption",
  `[exact dec_trivial]          >> pure "exact dec_trivial",
  applicable                    >> pure "applicable",
  force (intros >> skip)        >> pure "intros",
  force (fsplit)                >> pure "fsplit",
  force (dsimp_eq_mpr)          >> pure "dsimp [eq.mpr] {unfold_reducible := tt}", -- TODO split this up?
  unfold_projections'               >> pure "unfold_projections", -- TODO replace with library version
  `[simp]                       >> pure "simp",
  -- dsimp_hypotheses              >> pure "dsimp_hypotheses",  -- TODO replace with library version
  `[dsimp at * {unfold_reducible := tt}]              >> pure "dsimp at * {unfold_reducible := tt}",  -- TODO combine with unfolding projections in hypotheses
  automatic_induction           >> pure "automatic_induction",
  unfold_projections_hypotheses >> pure "unfold_projections_hypotheses",  -- TODO replace with library version
  tactic.interactive.congr_fun_assumptions, -- TODO perhaps this should be wrapped in if_exactly_one_goal? -- TODO are there other aggresssive things we can do?
  `[simp at *]                     >> pure "simp at *"
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