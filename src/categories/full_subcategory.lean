-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor
import categories.tactics.obviously

namespace category_theory

universes u₁ v₁ u₂ v₂ w₁

local attribute [backwards] category.id -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞 

instance SigmaCategory (Z : C → Type w₁) : category.{(max u₁ w₁) v₁} (Σ X : C, Z X) := 
{ Hom  := λ X Y, X.1 ⟶ Y.1,
  id   := by tidy,
  comp := λ _ _ _ f g, f ≫ g }

instance FullSubcategory (Z : C → Prop) : category.{u₁ v₁} {X : C // Z X} := 
{ Hom  := λ X Y, X.1 ⟶ Y.1,
  id   := by tidy,
  comp := λ _ _ _ f g, f ≫ g }

definition SigmaCategoryEmbedding {Z : C → Type u₁} : (Σ X : C, Z X) ↝ C := 
{ obj := λ X, X.1,
  map := λ _ _ f, f }

definition FullCategoryEmbedding {Z : C → Prop} : {X : C // Z X} ↝ C := 
{ obj := λ X, X.1,
  map := λ _ _ f, f }

-- PROJECT, show these are fully faithful

variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
include 𝒟 

definition Functor_restricts_to_SigmaCategory (F : C ↝ D) (ZC : C → Type u₁) (ZD : D → Type u₂) (w : ∀ {X : C} (z : ZC X), ZD (F X)) : (Σ X : C, ZC X) ↝ (Σ Y : D, ZD Y) := 
{ obj     := λ X, ⟨ F X.1, w X.2 ⟩,
  map   := λ _ _ f, F.map f }

definition Functor_restricts_to_FullSubcategory (F : C ↝ D) (ZC : C → Prop) (ZD : D → Prop) (w : ∀ {X : C} (z : ZC X), ZD (F X)) : {X : C // ZC X} ↝ {Y : D // ZD Y} := 
{ obj     := λ X, ⟨ F X.1, w X.2 ⟩,
  map   := λ _ _ f, F.map f }


end category_theory
