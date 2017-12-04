-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.at_least_one
import tidy.tidy_attributes

open tactic

inductive Two : Type
| _0 : Two
| _1 : Two

-- TODO ideally this wouldn't require a whole separate tactic, just an attribute on Two
@[tidy] meta def induction_Two : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(Two) := induction h >> skip | _ := failed end))
