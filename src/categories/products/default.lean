-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..functor_categories

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.products

universes u₁ v₁ u₂ v₂ 

definition ProductCategory (C D : Category) :
  Category :=
  {
    Obj      := C.Obj × D.Obj,
    Hom      := (λ X Y : C.Obj × D.Obj, C.Hom (X.fst) (Y.fst) × D.Hom (X.snd) (Y.snd)),
    identity := λ X, ⟨ C.identity (X.fst), D.identity (X.snd) ⟩,
    compose  := λ _ _ _ f g, (C.compose (f.fst) (g.fst), D.compose (f.snd) (g.snd))
 }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

definition RightInjectionAt {D : Category} (C : Category) (Z : D.Obj) : Functor C (C × D) :=
{onObjects     := λ X, (X, Z),
  onMorphisms   := λ X Y f, (f, D.identity Z)
}

definition LeftInjectionAt {C : Category} (Z : C.Obj) (D : Category) : Functor D (C × D) :=
{onObjects     := λ X, (Z, X),
  onMorphisms   := λ X Y f, (C.identity Z, f)
}

definition LeftProjection (C D : Category) : Functor (C × D) C := 
{
  onObjects     := λ X, X.1,
  onMorphisms   := λ X Y f, f.1
}

definition RightProjection (C D : Category) : Functor (C × D) D := 
{
  onObjects     := λ X, X.2,
  onMorphisms   := λ X Y f, f.2
}

definition ProductFunctor {A B C D : Category} (F : Functor A B) (G : Functor C D) : Functor (A × C) (B × D) :=
{
  onObjects     := λ X, (F.onObjects X.fst, G.onObjects X.snd),
  onMorphisms   := λ _ _ f, (F.onMorphisms f.fst, G.onMorphisms f.snd)
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

definition ProductNaturalTransformation
  {A B C D : Category} 
  {F G : Functor A B} {H I : Functor C D} 
  (α : NaturalTransformation F G) (β : NaturalTransformation H I) : 
    NaturalTransformation (F × H) (G × I) :=
{
  components := λ X, (α.components X.fst, β.components X.snd)
}

namespace ProductNaturalTransformation
  notation α `×` β := ProductNaturalTransformation α β
end ProductNaturalTransformation

variable (C : Category.{u1 v1})
variable (D : Category.{u2 v2})

definition Evaluation : Functor (ProductCategory (FunctorCategory C D) C) D := {
  onObjects     := λ p, p.1.onObjects p.2,
  onMorphisms   := λ x y f, D.compose (x.1.onMorphisms f.2) (f.1.components y.2)
}

end categories.products
