-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

-- Applies a list of tactics in turn, always succeeding.
meta def list_try_seq : list (tactic unit) → tactic unit 
| list.nil  := skip
| (t :: ts) := seq (try t) (list_try_seq ts)

-- Applies a list of tactics in turn, succeeding if at least one succeeds.
meta def at_least_one : list (tactic unit) → tactic unit
| list.nil  := fail "at_least_one tactic failed, no more tactics"
| (t :: ts) := (seq t (list_try_seq ts)) <|> (at_least_one ts)