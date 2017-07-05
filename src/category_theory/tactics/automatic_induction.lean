-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .at_least_one .Two

open tactic

meta def new_names ( e : expr ) : tactic (list name) :=
  do 
    n1 ← get_unused_name e.local_pp_name (some 1), 
    n2 ← get_unused_name e.local_pp_name (some 2),
    pure [ n1, n2 ] 

meta def automatic_induction_at (h : expr) : tactic unit :=
do t ← infer_type h,
match t with
| `(unit)      := induction h >>= λ x, skip
| `(punit)     := induction h >>= λ x, skip
| `(false)     := induction h >>= λ x, skip
| `(empty)     := induction h >>= λ x, skip
| `(fin nat.zero) := induction h >>= λ x, `[cases is_lt]
| `(Two)       := induction h >>= λ x, skip
| `(ulift _)   := induction h >>= λ x, skip
| `(plift _)   := induction h >>= λ x, skip
| `(eq _ _)    := induction h >>= λ x, skip
| `(prod _ _)  := do names ← new_names h,
                      induction h >> skip
| `(sigma _)   := do names ← new_names h,
                      induction h >> skip
| `(subtype _) := do names ← new_names h,
                      induction h names >> skip
| _              := failed
end

meta def automatic_induction : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, automatic_induction_at h))