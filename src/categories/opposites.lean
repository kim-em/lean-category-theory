-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .functor
import .products
import .types

open categories
open categories.functor
open categories.products
open categories.types

namespace categories.opposites

universes u₁ u₂

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

def op (C : Type u₁) : Type u₁ := C

notation C `ᵒᵖ` := op C

instance Opposite : category (Cᵒᵖ) :=
{ Hom := λ X Y : C, Hom Y X,
  compose  := λ _ _ _ f g, g ≫ f,
  identity := λ X, 𝟙 X }

definition OppositeFunctor (F : Functor C D) : Functor (Cᵒᵖ) (Dᵒᵖ) :=  {
  onObjects     := λ X, F.onObjects X,
  onMorphisms   := λ X Y f, F.onMorphisms f
}

definition HomPairing (C : Type (u₁+1)) [category C]: Functor.{u₁ u₁} (Cᵒᵖ × C) (Type u₁) := { 
  onObjects     := λ p, @Hom C _ p.1 p.2,
  onMorphisms   := λ X Y f, λ h, f.1 ≫ h ≫ f.2
}

-- PROJECT prove C^op^op is C
-- definition OppositeOpposite (C : Category) : Equivalence (Opposite (Opposite C)) C := sorry
-- PROJECT opposites preserve products, functors, slices.

-- @[simp,ematch] lemma ContravariantFunctor.functoriality
--   (F : Functor (Cᵒᵖ) D)
--   (X Y Z : C)
--   (f : Hom X Y) (g : Hom Y Z) :
--     F.onMorphisms ((f ≫ g) : Hom X Z) = (F.onMorphisms g) ≫ (F.onMorphisms f) := begin erw F.functoriality, end -- TODO automate?

-- @[simp,ematch] lemma ContravariantFunctor.identities
--   (F : Functor (Cᵒᵖ) D)
--   (X : C) :
--     F.onMorphisms (𝟙 X) = 𝟙 (F.onObjects X) := ♮

@[simp,ematch] lemma ContravariantFunctor.functoriality
  (F : Functor (Cᵒᵖ) D)
  (X Y Z : (Cᵒᵖ))
  (f : Hom X Y) (g : Hom Y Z) :
    F.onMorphisms ((@categories.category.compose C _ _ _ _ g f) : Hom X Z) = (F.onMorphisms f) ≫ (F.onMorphisms g) := by erw F.functoriality

@[simp,ematch] lemma ContravariantFunctor.identities
  (F : Functor (Cᵒᵖ) D) (X : (Cᵒᵖ)) : (F.onMorphisms (@categories.category.identity.{u₁} C _ X)) = 𝟙 (F.onObjects X) := by erw F.identities 

end categories.opposites