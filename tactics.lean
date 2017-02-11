-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

set_option pp.universes true

open smt_tactic

def applicandum_attribute : user_attribute := {
  name := `applicandum,
  descr := "Lemma that should be automatically applied to goals by the 'applico' tactic."
}

run_command attribute.register `applicandum_attribute

open tactic

/- Try to apply one of the given lemas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic unit
| []      := failed
| (c::cs) := (mk_const c >>= fapply) <|> any_apply cs

meta def applica : tactic unit :=
do cs ← attribute.get_instances `applicandum,
   repeat_at_most 3 (any_apply cs >> try intros)

meta def blast : tactic unit := repeat_at_most 3 ( (using_smt $ intros >> add_lemmas_from_facts >> repeat_at_most 3 ematch) >> applica >> try simp )

notation `♮` := by blast

def {u} auto_cast {α β : Type u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Type u} (a : α) : @auto_cast α α ♮ a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ ♮ p