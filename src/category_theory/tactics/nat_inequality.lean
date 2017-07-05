-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic
open nat

-- PROJECT make this less lame
meta def nat_inequality : tactic unit :=
do tgt ← target,
match tgt with
| `(%%lhs < %%rhs) := `[apply nat.lt_succ_of_le]     -- PROJECT how to check lhs and rhs are actually nat's?
| `(%%lhs ≤ %%rhs) := `[rewrite nat.le_iff_lt_or_eq, simp]
| _                := failed
end

-- lemma f : 0 < 2 :=
-- begin
--  nat_inequality,
--  nat_inequality,
--  nat_inequality,
--  nat_inequality,
-- end
