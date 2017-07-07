-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.tactics.at_least_one
import category_theory.tactics.tidy_tactics

open tactic

inductive Two : Type
| _0 : Two
| _1 : Two

-- TODO ideally this wouldn't require a whole separate tactic, just an attribute on Two
@[tidy] meta def induction_Two : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, do t ← infer_type h, match t with | `(Two) := induction h >> skip | _ := failed end))
