-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.tidy
import data.fintype

universes u v

open tactic

inductive Two : Type u
| _0 : Two
| _1 : Two

open Two

@[simp] lemma Two_0_eq_1_eq_false : ¬(_0 = _1) :=
by contradiction

@[simp] lemma Two_1_eq_0_eq_false : ¬(_1 = _0) :=
by contradiction

@[tidy] meta def induction_Two : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(Two) := cases h >> skip | _ := failed end))

instance Two_decidable : decidable_eq Two := by obviously

instance Two_fintype : fintype Two := {
  elems := [_0, _1].to_finset,
  complete := by obviously
}
