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

variable {C : Type u₁}
variable [category C]
variable {D : Type u₂}
variable [category D]

definition Opposite : category C :=
{
    Hom := λ X Y : C, Hom Y X,
    compose  := λ _ _ _ f g, g >> f,
    identity := λ X, 𝟙 X
}

definition OppositeFunctor (F : Functor C D) : @Functor C D (@Opposite _ _) (@Opposite _ _) :=
{
  onObjects     := λ X, F.onObjects X,
  onMorphisms   := λ X Y f, F.onMorphisms f
}

definition HomPairing {C : Type u₁} [category C]: @Functor (C × C) (Type u₁) (@products.ProductCategory _  (@Opposite _ _) _ _) _ :=
{
  onObjects     := λ p, Hom p.1 p.2,
  onMorphisms   := λ X Y f, λ g, ((f.1 : @Hom C _ Y.1 X.1) >> (g : @Hom C _ X.1 X.2)) >> f.2
  --λ X Y f, λ g : @Hom C _ X.1 X.2, (@category.compose _ C_cat _ _ _ (@category.compose _ C_cat _ _ _ (f.1 : @Hom C _ Y.1 X.1)  (g : @Hom C _ X.1 X.2)) (f.2 : @Hom C _ X.2 Y.2))
}

-- PROJECT prove C^op^op is C
-- definition OppositeOpposite (C : Category) : Equivalence (Opposite (Opposite C)) C := sorry
-- PROJECT opposites preserve products, functors, slices.

local attribute [reducible] Opposite

@[simp,ematch] lemma ContravariantFunctor.functoriality
  {C : Category}
  {D : Category}
  {F : Functor (Opposite C) D}
  {X Y Z : C.Obj}
  {f : C.Hom X Y} {g : C.Hom Y Z} :
    F.onMorphisms (C.compose f g) = D.compose (F.onMorphisms g) (F.onMorphisms f) := ♮ 

@[simp,ematch] lemma ContravariantFunctor.identities
  {C : Category}
  {D : Category}
  {F : Functor (Opposite C) D}
  {X : C.Obj} :
    F.onMorphisms (C.identity X) = D.identity (F.onObjects X) := ♮

end categories.opposites