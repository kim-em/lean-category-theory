-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.category
import categories.functor

namespace categories

universes u₁ u₂ 

open categories.functor

local attribute [applicable] uv_category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition discrete (α : Type u₁) := α

instance  DiscreteCategory (α : Type u₁) : small_category (discrete α) := {
  Hom            := λ X Y, ulift (plift (X = Y)),
  identity       := by obviously,
  compose        := by obviously
}

instance EmptyCategory : small_category pempty := (by apply_instance : small_category (discrete pempty))
instance OneCategory : small_category punit := (by apply_instance : small_category (discrete punit))

definition EmptyFunctor (C : Type (u₂+1)) [category C] : pempty ↝ C := by obviously

-- TODO find a home for these in mathlib. https://leanprover.zulipchat.com/#narrow/stream/113488-general/subject/transport.20through.20trivial.20bundles/near/125769004
@[simp] lemma plift.rec.constant {α : Sort u₁} {β : Sort u₂} (b : β) : @plift.rec α (λ _, β) (λ _, b) = λ _, b :=
begin 
  apply funext,
  intros,
  cases x,
  refl,
end
@[simp] lemma ulift.rec.constant {α : Type u₁} {β : Sort u₂} (b : β) : @ulift.rec α (λ _, β) (λ _, b) = λ _, b :=
begin 
  apply funext,
  intros,
  cases x,
  refl,
end

definition Functor.fromFunction {C : Type (u₂+1)} [category C] {I : Type (u₁+1)} (F : I → C) : (discrete I) ↝ C := {
  onObjects     := F,
  onMorphisms   := λ X Y f, begin cases f, cases f, cases f, exact 𝟙 (F X) end,
}

end categories
