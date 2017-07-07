-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .at_least_one

open tactic

def tidy_attribute : user_attribute := {
  name := `tidy,
  descr := "A tactic that should be called by tidy."
}

run_cmd attribute.register `tidy_attribute

meta def name_to_tactic ( n : name ) : tactic (tactic string) := 
do e ← mk_const n,
   (eval_expr (tactic string) e) <|> 
   (eval_expr (tactic unit) e) >>= (λ t, pure ( t >> pure n.to_string ))

meta def names_to_tactics ( n : list name ) : tactic (list (tactic string)) :=
do n.mfor name_to_tactic

meta def run_tidy_tactics : tactic string :=
do names ← attribute.get_instances `tidy,
   tactics ← names_to_tactics names,
   first tactics <|> fail "no @[tidy] tactics succeeded"