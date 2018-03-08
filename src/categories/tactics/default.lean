-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import tidy.applicable tidy.force tidy.at_least_one tidy.repeat_at_least_once tidy.smt tidy.tidy
import tidy.its
import tidy.auto_cast
import tidy.make_lemma

-- FIXME this is evil; work out where it's necessary, and have solve_by_elim fake it
@[simp] lemma {u v} funext_simp {α : Type u} {Z : α → Type v} {f g : Π a : α, Z a} : (f = g) = ∀ a : α, f a = g a :=
begin
  apply propext,
  split,
  { intro w, intro, rw w },
  { intro w, apply funext, assumption }
end 

open tactic

meta def trace_goal_type : tactic unit :=
do g ← target,
   tactic.trace g,
   infer_type g >>= tactic.trace,
   tactic.skip

set_option formatter.hide_full_terms false

set_option pp.proofs false

