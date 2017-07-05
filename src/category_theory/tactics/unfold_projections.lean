-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .at_least_one

open tactic

private meta def unfold_projections_core' (m : transparency) (e : expr) : tactic expr :=
let unfold (changed : bool) (e : expr) : tactic (bool × expr × bool) := do
  new_e ← unfold_proj e m,
  return (tt, new_e, tt)
in do (tt, new_e) ← dsimplify_core tt (λ c e, failed) unfold e | fail "no projections to unfold",
      return new_e

-- meta def unfold_projections' : tactic unit :=
-- target >>= unfold_projections_core' semireducible default_max_steps >>= change

meta def unfold_projections_at' (h : expr) : tactic unit :=
do num_reverted ← revert h,
   (expr.pi n bi d b : expr) ← target,
   new_d ← unfold_projections_core' semireducible d,
   change $ expr.pi n bi new_d b,
   intron num_reverted

meta def unfold_projections_hypotheses : tactic unit :=
do l ← local_context,
   s ← simp_lemmas.mk_default,
   at_least_one (l.reverse.for (λ h, unfold_projections_at' h)) <|> fail "fail no projections to unfold in hypotheses"   

meta def unfold_projections_hypotheses' : tactic unit := `[unfold_projs at *] -- BUG see the problem in discrete_category.lean

