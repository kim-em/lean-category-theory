-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..functor_categories

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.products

universes u₁ u₂ u₃ u₄

variable {A : Type (u₁+1)}
variable [category A]
variable {B : Type (u₂+1)}
variable [category B]
variable {C : Type (u₃+1)}
variable [category C]
variable {D : Type (u₄+1)}
variable [category D]

instance ProductCategory : category (C × D) := {
    Hom      := (λ X Y : C × D, Hom (X.1) (Y.1) × Hom (X.2) (Y.2)),
    identity := λ X, ⟨ 𝟙 (X.1), 𝟙 (X.2) ⟩,
    compose  := λ _ _ _ f g, (f.1 ≫ g.1, f.2 ≫ g.2)
 }

definition RightInjectionAt (Z : D) : Functor C (C × D) := {
  onObjects     := λ X, (X, Z),
  onMorphisms   := λ X Y f, (f, 𝟙 Z)
}

definition LeftInjectionAt (Z : C) : Functor D (C × D) := {
  onObjects     := λ X, (Z, X),
  onMorphisms   := λ X Y f, (𝟙 Z, f)
}

definition LeftProjection : Functor (C × D) C := 
{
  onObjects     := λ X, X.1,
  onMorphisms   := λ X Y f, f.1
}

definition RightProjection : Functor (C × D) D := 
{
  onObjects     := λ X, X.2,
  onMorphisms   := λ X Y f, f.2
}

definition ProductFunctor (F : Functor A B) (G : Functor C D) : Functor (A × C) (B × D) :=
{
  onObjects     := λ X, (F X.1, G X.2),
  onMorphisms   := λ _ _ f, (F &> f.1, G &> f.2)
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

definition ProductNaturalTransformation
  {F G : Functor A B} {H I : Functor C D} 
  (α : NaturalTransformation F G) (β : NaturalTransformation H I) : 
    NaturalTransformation (F × H) (G × I) :=
{
  components := λ X, (α.components X.1, β.components X.2)
}

namespace ProductNaturalTransformation
  notation α `×` β := ProductNaturalTransformation α β
end ProductNaturalTransformation


end categories.products
