-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .natural_transformation

-- set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.products

universe variables u1 v1 u2 v2 u3 v3 u4 v4

@[reducible] definition ProductCategory (C : Category.{u1 v1}) (D : Category.{u2 v2}) :
  Category :=
  {
    Obj      := C^.Obj × D^.Obj,
    Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd)),
    identity := λ X, ⟨ C^.identity (X^.fst), D^.identity (X^.snd) ⟩,
    compose  := λ _ _ _ f g, pprod.mk (C^.compose (f^.fst) (g^.fst)) (D^.compose (f^.snd) (g^.snd)),

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

@[reducible] definition LeftInjectionAt { D : Category.{u2 v2} } ( Z : D^.Obj ) ( C : Category.{u1 v1} ) : Functor C (C × D) :=
{ onObjects     := λ X, pprod.mk X Z,
  onMorphisms   := λ X Y f, pprod.mk f (D^.identity Z),
  identities    := ♮,
  functoriality := ♮
}

@[reducible] definition RightInjectionAt { C : Category.{u1 v1} } ( Z : C^.Obj) ( D : Category.{u2 v2} ) : Functor D (C × D) :=
{ onObjects     := λ X, pprod.mk Z X,
  onMorphisms   := λ X Y f, pprod.mk (C^.identity Z) f,
  identities    := ♮,
  functoriality := ♮
}

@[reducible] definition ProductFunctor { A : Category.{u1 v1} } { B : Category.{u2 v2} } { C : Category.{u3 v3} } { D : Category.{u4 v4} } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects     := λ X, pprod.mk (F X^.fst) (G X^.snd),
  onMorphisms   := λ _ _ f, pprod.mk (F^.onMorphisms f^.fst) (G^.onMorphisms f^.snd),
  identities    := ♮,
  functoriality := ♮
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

@[reducible] definition ProductNaturalTransformation
  { A B C D : Category } 
  { F G : Functor A B } { H I : Functor C D } 
  (α : NaturalTransformation F G) (β : NaturalTransformation H I) : 
    NaturalTransformation (F × H) (G × I) :=
{
  components := λ X, pprod.mk (α X^.fst) (β X^.snd),
  naturality := ♮
}

namespace ProductNaturalTransformation
  notation α `×` β := ProductNaturalTransformation α β
end ProductNaturalTransformation

@[reducible] definition SwitchProductCategory ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, pprod.mk X^.snd X^.fst,
  onMorphisms   := λ _ _ f, pprod.mk f^.snd f^.fst,
  identities    := ♮,
  functoriality := ♮
}

lemma switch_twice_is_the_identity
  ( C D : Category ) :
  FunctorComposition ( SwitchProductCategory C D ) ( SwitchProductCategory D C ) = IdentityFunctor (ProductCategory C D) := ♮

@[reducible] definition ProductCategoryAssociator
  ( C : Category.{ u1 v1 } )
  ( D : Category.{ u2 v2 } )
  ( E : Category.{ u3 v3 } )
  : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, pprod.mk X^.fst^.fst (pprod.mk X^.fst^.snd X^.snd),
  onMorphisms   := λ _ _ f, pprod.mk f^.fst^.fst (pprod.mk f^.fst^.snd f^.snd),
  identities    := ♮,
  functoriality := ♮
}

-- @[ematch] lemma bifunctor_left_identity
--   { C D E : Category }
--   ( W : C^.Obj ) ( X Y Z : D^.Obj )
--   ( f : D X Y ) ( g : D Y Z )
--   ( F : Functor (C × D) E ) :
--     @Functor.onMorphisms _ _ F (W, X) (W, Z) (C^.identity W, D^.compose f g ) 
--     = E^.compose
--         (@Functor.onMorphisms _ _ F (W, X) (W, Y) (C^.identity W, f )) 
--         (@Functor.onMorphisms _ _ F (W, Y) (W, Z) (C^.identity W, g )) := ♮

-- @[simp] lemma bifunctor_identities
--   { C D E : Category }
--   ( X : C^.Obj ) ( Y : D^.Obj )
--   ( F : Functor (C × D) E ) : @Functor.onMorphisms _ _ F (X, Y) (X, Y) (C^.identity X, D^.identity Y) = E^.identity (F^.onObjects (X, Y)) :=
--   begin
--     assert p : (C^.identity X, D^.identity Y) = (C × D)^.identity (X, Y), blast,
--     rewrite p,
--     rewrite F^.identities
--   end 

end tqft.categories.products
