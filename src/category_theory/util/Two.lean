-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.tactics.obviously
import data.fintype

universes u v

@[derive decidable_eq]
inductive Two : Type u
| _0 : Two
| _1 : Two

open Two

section
open tactic
@[tidy] meta def induction_Two : tactic unit :=
do l ← local_context,
   r ← successes (l.reverse.map (λ h, do t ← infer_type h, match t with | `(Two) := cases h >> skip | _ := failed end)),
   when (r.empty) failed
end

instance Two_fintype : fintype Two := 
{ elems       := [_0, _1].to_finset,
  complete    := by tidy }
