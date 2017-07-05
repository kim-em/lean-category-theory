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
| `(unit)      := induction h >> skip
| `(punit)     := induction h >> skip
| `(false)     := induction h >> skip
| `(empty)     := induction h >> skip
| `(fin nat.zero) := induction h >> `[cases is_lt]
| `(Two)       := induction h >> skip
| `(ulift _)   := induction h >> skip
| `(plift _)   := induction h >> skip
| `(eq _ _)    := induction h >> skip
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