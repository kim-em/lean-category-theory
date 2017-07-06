-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic


def tidy_attribute : user_attribute := {
  name := `tidy,
  descr := "A tactic that should be called by tidy."
}

run_cmd attribute.register `tidy_attribute

-- meta def run_tactics : list name → tactic unit
-- | []      := failed
-- | (c::cs) := (mk_const c >>= λ e, sorry)

-- meta def run_tidy_tactics : tactic unit :=
-- do tactics ← attribute.get_instances `tidy,
--    (run_tactics tactics) <|> fail "no @[tidy] tactics succeeded"
