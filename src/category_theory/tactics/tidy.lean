-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .congr_fun_assumptions .fsplit .simp_hypotheses .dsimp_hypotheses .automatic_induction .unfold_projections .tidy_tactics
import .chain
import .smt

open tactic

private meta def dsimp_eq_mpr : tactic unit := `[dsimp [eq.mpr] {unfold_reducible := tt}]

meta def if_exactly_one_goal { α : Type } ( t : tactic α ) : tactic α :=
do ng ← num_goals,
   if ng = 1 then t else fail "there is not exactly one goal"

private meta def propositional_goals_core { α : Type } (tac : tactic α) : list expr → list expr →  (list (option α)) → bool → tactic (list (option α))
| []        ac results progress := guard progress >> set_goals ac >> pure results
| (g :: gs) ac results progress :=
  do t ← infer_type g,
     p ← is_prop t,
     if p then do {
        set_goals [g],
        succeeded ← try_core tac,
        new_gs    ← get_goals,
        propositional_goals_core gs (ac ++ new_gs) (succeeded :: results ) (succeeded.is_some || progress)
     } else do {
       propositional_goals_core gs (ac ++ [ g ]) (none :: results) progress
     }

/-- Apply the given tactic to any propositional goal where it succeeds. The tactic succeeds only if
   tac succeeds for at least one goal. -/
meta def propositional_goals { α : Type } ( t : tactic α ) : tactic (list (option α)) :=
do gs ← get_goals,
   results ← propositional_goals_core t gs [] [] ff,
   pure results.reverse

/-
-- For now:
-- If there is just one goal, applies the tactic.
-- Otherwise, applies the tactic to all propositional goals,
-- Succeeds if the tactic succeeds on at least one goal.
-- 
-- Eventually I'd like to pick out all goals which no later goal depends on.
-/
meta def independent_goals { α : Type } ( t : tactic α ) : tactic (list (option α)) :=
do ng ← num_goals,
   if ng = 1 then
     t >>= λ r, pure [ some r ]
   else 
     propositional_goals t

meta def build_focus_string ( s : list ( option string ) ) : tactic string := 
pure ("focus " ++ (s.map(λ x, option.get_or_else x "skip")).to_string)

meta def if_first_goal_safe { α : Type } ( t : tactic α ) : tactic α :=
do ng ← num_goals,
   if ng = 1 then t else do {
    -- ty ← target >>= infer_type,
    -- p ← is_prop ty,
     p ← target >>= is_prop,
     if p then t else fail "there are multiple goals, and the first goal is not a mere proposition"
   }


meta def global_tidy_tactics : list (tactic string) :=
[
  triv                                                >> pure "triv", 
  force (reflexivity)                                 >> pure "refl", 
  if_first_goal_safe assumption                       >> pure "assumption",
  -- independent_goals (assumption >> pure "assumption") >>= build_focus_string,
  `[exact dec_trivial]                                >> pure "exact dec_trivial",
  applicable                                          >> pure "applicable",
  force (intros >> skip)                              >> pure "intros",
  force (fsplit)                                      >> pure "fsplit", -- TODO is fapply necessary anymore?
  force (dsimp_eq_mpr)           >> pure "dsimp [eq.mpr] {unfold_reducible := tt}", -- TODO split this up?
  unfold_projections'            >> pure "unfold_projections", -- TODO replace with library version
  `[simp]                        >> pure "simp",
  `[simp *]                        >> pure "simp *",
  `[dsimp at * {unfold_reducible := tt}]              >> pure "dsimp at * {unfold_reducible := tt}",  -- TODO combine with unfolding projections in hypotheses
  automatic_induction            >> pure "automatic_induction",
  unfold_projections_hypotheses  >> pure "unfold_projections_hypotheses",  -- TODO replace with library version
  -- (independent_goals congr_fun_assumptions)  >>= build_focus_string, 
  if_first_goal_safe congr_fun_assumptions, -- TODO are there other aggresssive things we can do?
  `[simp at * {max_steps := 50}]                     >> pure "simp at *"
]

meta structure tidy_cfg :=
( max_steps : nat                      := chain_default_max_steps )
( trace_progress : bool                := ff )
( run_annotated_tactics : bool         := tt )
( extra_tactics : list (tactic string) := [] )

meta def tidy ( cfg : tidy_cfg := {} ) : tactic unit :=
let tidy_tactics := global_tidy_tactics ++ (if cfg.run_annotated_tactics then [ run_tidy_tactics ] else []) ++ cfg.extra_tactics in
   do results ← chain tidy_tactics cfg.max_steps,
   if cfg.trace_progress then
     trace ("... chain tactic used: " ++ results.to_string)
   else
     skip

-- TODO is 'any_goals' really a good idea here?
meta def blast ( cfg : tidy_cfg := {} ) : tactic unit := 
tidy { cfg with extra_tactics := cfg.extra_tactics ++ [ any_goals ( smt_eblast >> done ) >> pure "smt_eblast" ] }

notation `♮` := by abstract { smt_eblast }
notation `♯` := by abstract { blast }