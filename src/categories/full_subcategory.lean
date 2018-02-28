-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .functor

open categories.functor

namespace categories

universes u₁ u₂ w wc wd

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]



instance SigmaCategory (Z : C → Type u₁) : category (Σ X : C, Z X) := {
  Hom := λ X Y, X.1 ⟶ Y.1,
  identity       := by tidy,
  compose        := λ _ _ _ f g, f ≫ g
}

instance FullSubcategory (Z : C → Prop) : category {X : C // Z X} := {
  Hom := λ X Y, X.1 ⟶ Y.1,
  identity       := by tidy,
  compose        := λ _ _ _ f g, f ≫ g
}

definition FullSubcategoryInclusion {Z : C → Type u₁} : Functor (Σ X : C, Z X) C := {
  onObjects := λ X, X.1,
  onMorphisms := λ _ _ f, f
}
-- PROJECT, also Prop version, and show these are fully faithful

definition Functor_restricts_to_FullSubcategory 
  (F : Functor C D) 
  (ZC : C → Type u₁)
  (ZD : D → Type u₂)
  (w : ∀ {X : C} (z : ZC X), ZD (F X)) : Functor (Σ X : C, ZC X) (Σ Y : D, ZD Y) := {
    onObjects     := λ X, ⟨ F X.1, w X.2 ⟩,
    onMorphisms   := λ _ _ f, F &> f
 }

end categories
