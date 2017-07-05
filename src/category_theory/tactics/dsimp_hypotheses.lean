-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .at_least_one

open tactic

-- -- We need our own version of dsimp_at_core, which fails when it can't do anything.
-- meta def dsimp_at_core' (s : simp_lemmas) (h : expr) : tactic unit :=
-- do num_reverted : ℕ ← revert h,
--    expr.pi n bi d b ← target,
--    h_simp ← s.dsimplify d,
--    guard (h_simp ≠ d) <|> fail "dsimp tactic did not simplify",
--    change $ expr.pi n bi h_simp b,
--    intron num_reverted

-- meta def dsimp_at' (h : expr) : tactic unit :=
-- do s ← simp_lemmas.mk_default, dsimp_at_core' s h

-- meta def dsimp_hypotheses : tactic unit :=
-- do l ← local_context,
--    at_least_one (l.reverse.for (λ h, dsimp_at' h)) <|> fail "dsimp could not simplify any hypothesis"

meta def dsimp_hypotheses : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, dsimp_hyp h)) <|> fail "dsimp could not simplify any hypothesis"