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

inductive op (C : Type u₁) : Type u₁
| op : C → op

notation C `ᵒᵖ` := op C

variable {C : Type u₁}
variable [category C]
variable {D : Type u₂}
variable [category D]

def op.of : Cᵒᵖ  → C
| (op.op X) := X

instance opposite_coercion_1 : has_coe (Cᵒᵖ) C :=
  {coe := op.of}
instance opposite_coercion_2 : has_coe C (Cᵒᵖ) :=
  {coe := op.op}

instance Opposite : category (Cᵒᵖ):=
{
    Hom := λ X Y, Hom (Y : C) (X : C),
    compose  := λ _ _ _ f g, g >> f,
    identity := λ X, 𝟙 X
}

definition OppositeFunctor (F : Functor C D) : Functor (Cᵒᵖ) (Dᵒᵖ) :=
{
  onObjects     := λ X, F.onObjects X,
  onMorphisms   := λ X Y f, F.onMorphisms f
}

definition HomPairing (C : Type u₁) : Functor ((Cᵒᵖ) × C) (Type u₁) :=
{
  onObjects     := λ p, C.Hom p.1 p.2,
  onMorphisms   := λ _ _ f, λ g, C.compose (C.compose f.1 g) f.2
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