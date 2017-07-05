-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

meta def force { α : Type } (t : tactic α) : tactic α :=
  do 
     goals ← get_goals,
     result ← t,
     goals' ← get_goals,
     guard (goals ≠ goals') <|> fail "force tactic failed",
     return result

namespace tactic.interactive
  meta def force (t : itactic) : tactic unit := _root_.force t
end tactic.interactive