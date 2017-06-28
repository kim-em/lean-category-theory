-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..natural_transformation

-- set_option pp.universes true

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

definition ProductCategory (C D : Category) :
  Category :=
  {
    Obj      := C.Obj × D.Obj,
    Hom      := (λ X Y : C.Obj × D.Obj, C.Hom (X.fst) (Y.fst) × D.Hom (X.snd) (Y.snd)),
    identity := λ X, ⟨ C.identity (X.fst), D.identity (X.snd) ⟩,
    compose  := λ _ _ _ f g, (C.compose (f.fst) (g.fst), D.compose (f.snd) (g.snd)),

    left_identity  := begin intros, simp, end,
    right_identity := begin intros, simp, end,
    associativity  := ♮
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

definition RightInjectionAt { D : Category } ( C : Category ) ( Z : D.Obj ) : Functor C (C × D) :=
{ onObjects     := λ X, (X, Z),
  onMorphisms   := λ X Y f, (f, D.identity Z),
  identities    := ♮,
  functoriality := ♯
}

definition LeftInjectionAt { C : Category } ( Z : C.Obj) ( D : Category ) : Functor D (C × D) :=
{ onObjects     := λ X, (Z, X),
  onMorphisms   := λ X Y f, (C.identity Z, f),
  identities    := ♮,
  functoriality := ♯
}

definition LeftProjection ( C D : Category ) : Functor (C × D) C := 
{
  onObjects     := λ X, X.1,
  onMorphisms   := λ X Y f, f.1,
  identities    := ♮,
  functoriality := ♮
}

definition RightProjection ( C D : Category ) : Functor (C × D) D := 
{
  onObjects     := λ X, X.2,
  onMorphisms   := λ X Y f, f.2,
  identities    := ♮,
  functoriality := ♮
}

definition ProductFunctor { A B C D : Category } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects     := λ X, (F.onObjects X.fst, G.onObjects X.snd),
  onMorphisms   := λ _ _ f, (F.onMorphisms f.fst, G.onMorphisms f.snd),
  identities    := ♯,
  functoriality := ♯
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

definition ProductNaturalTransformation
  { A B C D : Category } 
  { F G : Functor A B } { H I : Functor C D } 
  (α : NaturalTransformation F G) (β : NaturalTransformation H I) : 
    NaturalTransformation (F × H) (G × I) :=
{
  components := λ X, (α.components X.fst, β.components X.snd),
  naturality := ♯  
}

namespace ProductNaturalTransformation
  notation α `×` β := ProductNaturalTransformation α β
end ProductNaturalTransformation

definition {u1 v1 u2 v2} Evaluation ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) : Functor (ProductCategory (FunctorCategory C D) C) D := {
  onObjects     := λ p, p.1.onObjects p.2,
  onMorphisms   := λ x y f, D.compose (x.1.onMorphisms f.2) (f.1.components y.2),
  identities    := ♯,
  functoriality := ♯
}

end categories.products
