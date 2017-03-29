-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .natural_transformation

-- set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.products

@[unfoldable] definition ProductCategory (C D : Category) :
  Category :=
  {
    Obj      := C^.Obj × D^.Obj,
    Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd)),
    identity := λ X, ⟨ C^.identity (X^.fst), D^.identity (X^.snd) ⟩,
    compose  := λ _ _ _ f g, (C^.compose (f^.fst) (g^.fst), D^.compose (f^.snd) (g^.snd)),

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

@[unfoldable] definition RightInjectionAt { D : Category } ( Z : D^.Obj ) ( C : Category ) : Functor C (C × D) :=
{ onObjects     := λ X, (X, Z),
  onMorphisms   := λ X Y f, (f, D^.identity Z),
  identities    := ♮,
  functoriality := ♯
}

@[unfoldable] definition LeftInjectionAt { C : Category } ( Z : C^.Obj) ( D : Category ) : Functor D (C × D) :=
{ onObjects     := λ X, (Z, X),
  onMorphisms   := λ X Y f, (C^.identity Z, f),
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

@[unfoldable] definition ProductFunctor { A B C D : Category } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects     := λ X, (F X^.fst, G X^.snd),
  onMorphisms   := λ _ _ f, (F^.onMorphisms f^.fst, G^.onMorphisms f^.snd),
  identities    := ♯,
  functoriality := ♯
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

@[unfoldable] definition ProductNaturalTransformation
  { A B C D : Category } 
  { F G : Functor A B } { H I : Functor C D } 
  (α : NaturalTransformation F G) (β : NaturalTransformation H I) : 
    NaturalTransformation (F × H) (G × I) :=
{
  components := λ X, (α X^.fst, β X^.snd),
  naturality := ♯
}

namespace ProductNaturalTransformation
  notation α `×` β := ProductNaturalTransformation α β
end ProductNaturalTransformation

definition SwitchProductCategory ( C D : Category ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X^.snd, X^.fst),
  onMorphisms   := λ _ _ f, (f^.snd, f^.fst),
  identities    := ♮,
  functoriality := ♮
}

lemma switch_twice_is_the_identity
  ( C D : Category ) :
  FunctorComposition ( SwitchProductCategory C D ) ( SwitchProductCategory D C ) = IdentityFunctor (ProductCategory C D) := ♯

@[unfoldable] definition ProductCategoryAssociator
  ( C D E: Category )
  : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, (X.1.1, (X.1.2, X.2)),
  onMorphisms   := λ _ _ f, (f.1.1, (f.1.2, f.2)),
  identities    := ♮,
  functoriality := ♮
}

@[unfoldable] definition ProductCategoryInverseAssociator
  ( C D E: Category )
  : Functor (C × (D × E)) ((C × D) × E) :=
{
  onObjects     := λ X, ((X.1, X.2.1), X.2.2),
  onMorphisms   := λ _ _ f, ((f.1, f.2.1), f.2.2),
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
