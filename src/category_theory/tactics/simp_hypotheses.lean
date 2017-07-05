-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .at_least_one

open tactic

-- We make a local version of simp_at, which only succeeds if it changes something, *and* successfully clears the old hypothesis.
meta def simp_at' (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk_default,
   S     ← S.append extra_lemmas,
   (new_htype, heq) ← simplify S htype cfg,
   guard (new_htype ≠ htype) <|> fail "simp_at didn't do anything",
   assert (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   clear h <|> fail "simp_at' could not clear the original hypothesis"

meta def simp_hypotheses : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, simp_at' h)) <|> fail "simp_hypothesis did not simplify anything"

meta def simp_hypotheses' : tactic unit := `[simp at *] -- FIXME useless at the moment, since this always succeeds