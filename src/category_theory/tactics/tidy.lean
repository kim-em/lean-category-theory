-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .congr_assumptions .fsplit .automatic_induction .tidy_tactics
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

meta def build_focus_string ( s : list ( option string ) ) : tactic string := 
pure ("focus " ++ (s.map(λ x, option.get_or_else x "skip")).to_string)

meta def if_first_goal_safe { α : Type } ( t : tactic α ) : tactic α :=
do ng ← num_goals,
   if ng = 1 then t else do {
     p ← target >>= is_prop,
     if p then t else fail "there are multiple goals, and the first goal is not a mere proposition"
   }


meta def global_tidy_tactics : list (tactic string) :=
[
  triv                                        >> pure "triv", 
  force (reflexivity)                         >> pure "refl", 
  if_first_goal_safe assumption               >> pure "assumption",
  -- if_first_goal_safe cc                       >> pure "cc", -- TODO try this?
  if_first_goal_safe congr_assumptions,      -- TODO are there other aggresssive things we can do?
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  applicable                                  >> pure "applicable",
  force (intros >> skip)                      >> pure "intros",
  force (fsplit)                              >> pure "fsplit", 
  force (dsimp_eq_mpr)                        >> pure "dsimp [eq.mpr] {unfold_reducible := tt}",
  unfold_projs_target {md := semireducible}   >> pure "unfold_projs_target {md := semireducible}", 
  `[simp]                                     >> pure "simp",
  automatic_induction                         >> pure "automatic_induction",
  `[dsimp at * {unfold_reducible := tt}]      >> pure "dsimp at * {unfold_reducible := tt}",
  `[unfold_projs at * {md := semireducible}]  >> pure "unfold_projs at * {md := semireducible}",
  `[simp at *]                                >> pure "simp at *"
]

meta structure tidy_cfg extends chain_cfg :=
( trace_result          : bool                 := ff )
( run_annotated_tactics : bool                 := tt )
( extra_tactics         : list (tactic string) := [] )

meta def tidy ( cfg : tidy_cfg := {} ) : tactic unit :=
let tidy_tactics := global_tidy_tactics ++ (if cfg.run_annotated_tactics then [ run_tidy_tactics ] else []) ++ cfg.extra_tactics in
   do results ← chain tidy_tactics cfg.to_chain_cfg,
   if cfg.trace_result then
     trace ("... chain tactic used: " ++ results.to_string)
   else
     skip

meta def blast ( cfg : tidy_cfg := {} ) : tactic unit := 
tidy { cfg with extra_tactics := cfg.extra_tactics ++ [ focus1 ( smt_eblast >> done ) >> pure "smt_eblast" ] }

notation `♮` := by abstract { smt_eblast }
notation `♯`  := by abstract { blast }