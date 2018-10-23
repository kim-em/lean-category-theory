-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor
import category_theory.equivalence

namespace category_theory

universes u₁ v₁ u₂ v₂

def discrete (α : Type u₁) := α

instance discrete_category (α : Type u₁) : small_category (discrete α) :=
{ hom  := λ X Y, ulift (plift (X = Y)),
  id   := by obviously,
  comp := by obviously }

instance pempty_category : small_category pempty := (by apply_instance : small_category (discrete pempty))

instance punit_category : category.{u₁ v₁} punit :=
{ hom  := λ X Y, punit,
  id   := by obviously,
  comp := by obviously }

example : equivalence.{u₁ u₁ u₁ u₁} punit (discrete punit) := by obviously

def functor.empty (C : Type (u₂+1)) [large_category C] : pempty ⥤ C := by obviously

-- TODO find a home for these in mathlib. https://leanprover.zulipchat.com/#narrow/stream/113488-general/subject/transport.20through.20trivial.20bundles/near/125769004
@[simp] lemma plift.rec.constant {α : Sort u₁} {β : Sort u₂} (b : β) : @plift.rec α (λ _, β) (λ _, b) = λ _, b :=
funext (λ x, plift.cases_on x (λ a, eq.refl (plift.rec (λ a', b) {down := a})))

@[simp] lemma ulift.rec.constant {α : Type u₁} {β : Sort u₂} (b : β) : @ulift.rec α (λ _, β) (λ _, b) = λ _, b :=
funext (λ x, ulift.cases_on x (λ a, eq.refl (ulift.rec (λ a', b) {down := a})))

def functor.of_function {C : Type u₂} [category.{u₂ v₂} C] {I : Type u₁} (F : I → C) : (discrete I) ⥤ C :=
{ obj := F,
  map' := λ X Y f, begin cases f, cases f, cases f, exact 𝟙 (F X) end }

end category_theory
