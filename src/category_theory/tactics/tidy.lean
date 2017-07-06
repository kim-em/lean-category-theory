-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .congr_fun_assumptions .fsplit .simp_hypotheses .dsimp_hypotheses .automatic_induction .unfold_projections
import .chain
import .smt

open tactic

private meta def dsimp_eq_mpr : tactic unit := `[dsimp [eq.mpr] {single_pass := tt, unfold_reducible := tt}]

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
  dsimp_hypotheses              >> pure "dsimp_hypotheses",  -- TODO replace with library version
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

-- set_option pp.all true
-- lemma f ( a b : nat → nat ) ( p : (a ∘ b) 0 = 0 ) : a ( b 0 ) = 0 :=
-- begin
-- -- -- All we need to do is unfold the function composition in the hypothesis p.

-- -- -- I would have tried:
-- -- dsimp at p,                          
-- -- -- but this fails with 'dsimplify tactic failed to simplify'.
-- -- -- Next, let's try the old behaviour of dsimp:
-- -- dsimp at p { unfold_reducible:=tt },
-- -- -- but this runs until eventually hitting max_steps!

-- -- -- We can see why the above tactic loops, by calling dsimp with single_pass:=tt:
-- dsimp at p { unfold_reducible:=tt,  single_pass:=tt },
-- -- -- gives 'p : @eq.{1} nat (a (b nat.zero)) nat.zero'
-- dsimp at p { unfold_reducible:=tt,  single_pass:=tt },
-- -- -- gives 'p : @eq.{1} nat (a (b (@has_zero.zero.{0} nat nat.has_zero))) (@has_zero.zero.{0} nat nat.has_zero)'
-- dsimp at p { unfold_reducible:=tt,  single_pass:=tt },
-- -- -- gives 'p : @eq.{1} nat (a (b nat.zero)) nat.zero'

-- -- -- (Perhaps it's worth mentioning that 'dsimp at p { unfold_reducible:=tt }' is successfully unfolding the function composition...
-- -- -- It just doing too much more besides.)
-- end