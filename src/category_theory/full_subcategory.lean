-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor
import category_theory.embedding

namespace category_theory

universes u₁ v₁ u₂ v₂ w₁

local attribute [back] category.id -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞 

instance sigma_category (Z : C → Type w₁) : category.{(max u₁ w₁) v₁} (Σ X : C, Z X) := 
{ hom  := λ X Y, X.1 ⟶ Y.1,
  id   := by obviously,
  comp := λ _ _ _ f g, f ≫ g }

instance full_subcategory (Z : C → Prop) : category.{u₁ v₁} {X : C // Z X} := 
{ hom  := λ X Y, X.1 ⟶ Y.1,
  id   := by obviously,
  comp := λ _ _ _ f g, f ≫ g }

def sigma_category_embedding (Z : C → Type u₁) : (Σ X : C, Z X) ⥤ C := 
{ obj := λ X, X.1,
  map' := λ _ _ f, f }

def full_subcategory_embedding (Z : C → Prop) : {X : C // Z X} ⥤ C := 
{ obj := λ X, X.1,
  map' := λ _ _ f, f }

-- move out/simplify dependencies
instance full_σ        (Z : C → Type u₁) : full    (sigma_category_embedding Z)    := by obviously
instance full_full     (Z : C → Prop)    : full     (full_subcategory_embedding Z) := by obviously
instance faithful_σ    (Z : C → Type u₁) : faithful (sigma_category_embedding Z)   := by obviously
instance faithful_full (Z : C → Prop)    : faithful (full_subcategory_embedding Z) := by obviously

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟 

def restrict_functor_σ (F : C ⥤ D) (ZC : C → Type u₁) (ZD : D → Type u₂) (w : ∀ {X : C} (z : ZC X), ZD (F X)) : (Σ X : C, ZC X) ⥤ (Σ Y : D, ZD Y) := 
{ obj := λ X, ⟨ F X.1, w X.2 ⟩,
  map' := λ _ _ f, F.map f }

def restrict_functor (F : C ⥤ D) (ZC : C → Prop) (ZD : D → Prop) (w : ∀ {X : C} (z : ZC X), ZD (F X)) : {X : C // ZC X} ⥤ {Y : D // ZD Y} := 
{ obj := λ X, ⟨ F X.1, w X.2 ⟩,
  map' := λ _ _ f, F.map f }

end category_theory
