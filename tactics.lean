-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

set_option pp.universes true

open smt_tactic

def pointwise_attribute : user_attribute := {
  name := `pointwise,
  descr := "A lemma that proves things are equal using the fact they are pointwise equal."
}

run_command attribute.register `pointwise_attribute

open tactic

/- Try to apply one of the given lemas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic unit
| []      := failed
| (c::cs) := (mk_const c >>= fapply) <|> any_apply cs

meta def smt   : tactic unit := using_smt $ intros >> add_lemmas_from_facts >> try ematch

meta def pointwise : tactic unit :=
do cs ← attribute.get_instances `pointwise,
   try (any_apply cs >> repeat_at_most 2 smt)

meta def blast : tactic unit := smt >> pointwise >> try simp

notation `♮` := by blast

def {u} auto_cast {α β : Type u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Type u} (a : α) : @auto_cast α α ♮ a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ ♮ p