-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation
import .opposites
import .products
import .isomorphism
import .examples.types.types

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.isomorphism
open tqft.categories.examples.types

namespace tqft.categories.adjunction

@[reducible] definition Triangle_1
  { C D : Category }
  { L : Functor C D }
  { R : Functor D C }
  ( unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
  ( counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) ) :=
  @vertical_composition_of_NaturalTransformations D C R (FunctorComposition (FunctorComposition R L) R) R ⟦ whisker_on_left R unit ⟧ ⟦ whisker_on_right counit R ⟧
  = IdentityNaturalTransformation R

@[reducible] definition Triangle_2
  { C D : Category }
  { L : Functor C D }
  { R : Functor D C }
  ( unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
  ( counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) ) :=
  @vertical_composition_of_NaturalTransformations C D L (FunctorComposition (FunctorComposition L R) L) L ⟦ whisker_on_right unit L ⟧ ⟦ whisker_on_left L counit ⟧
  = IdentityNaturalTransformation L

structure Adjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  ( unit          : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
  ( counit        : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) )
  ( triangle_1    : Triangle_1 unit counit )
  ( triangle_2    : Triangle_2 unit counit )

@[ematch] lemma Adjunction.unit_naturality
  { C D : Category } 
  { L : Functor C D } { R : Functor D C } 
  ( A : Adjunction L R ) 
  { X Y : C.Obj } ( f : C.Hom X Y ) : C.compose f (A.unit.components Y) = C.compose (A.unit.components X) (R.onMorphisms (L.onMorphisms f)) :=
  begin
    refine ( cast _ (A.unit.naturality f) ),
    blast
  end
@[ematch] lemma Adjunction.counit_naturality
  { C D : Category } 
  { L : Functor C D } { R : Functor D C } 
  ( A : Adjunction L R ) 
  { X Y : D.Obj } ( f : D.Hom X Y ) : D.compose (L.onMorphisms (R.onMorphisms f)) (A.counit.components Y) = D.compose (A.counit.components X) f :=
  begin
    refine ( cast _ (A.counit.naturality f) ),
    blast
  end

local attribute [pointwise] funext

@[unfoldable] definition { u v } HomPairing ( C : Category.{u v} ) : Functor ((Opposite C) × C) CategoryOfTypes.{v} :=
{
  onObjects     := λ p, C.Hom p.1 p.2,
  onMorphisms   := λ X F f, λ g, C.compose (C.compose f.1 g) f.2,
  identities    := ♯,
  functoriality := ♯
}

@[unfoldable] definition HomAdjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  NaturalIsomorphism
    (FunctorComposition (OppositeFunctor L × IdentityFunctor D) (HomPairing D))
    (FunctorComposition (IdentityFunctor (Opposite C) × R) (HomPairing C))

definition Adjunctions_agree { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :
  Isomorphism CategoryOfTypes (Adjunction L R) (HomAdjunction L R) := 
{
  morphism  := λ A, {
    morphism  := {
      components := λ P, 
        -- We need to construct the map from D.Hom (L P.1) P.2 to D.Hom P.1 (R P.2)
        λ f, C.compose (A.unit P.1) (R.onMorphisms f),
      naturality := begin
                      blast,
                      repeat { rewrite - C.associativity },
                      erewrite A.unit_naturality,
                      blast
                    end
    },
    inverse   := {
      components := λ P, 
        -- We need to construct the map back to D.Hom (L P.1) P.2 from D.Hom P.1 (R P.2)
        λ f, D.compose (L.onMorphisms f) (A.counit P.2),
      naturality := begin
                      blast,
                      repeat { rewrite D.associativity },
                      erewrite - A.counit_naturality,
                      blast
                    end
    },
    witness_1 := begin
                   blast,
                   
                   admit
                 end,
    witness_2 := sorry
  },
  inverse   := sorry,
  witness_1 := sorry,
  witness_2 := sorry
}

-- PROJECT examples
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end tqft.categories.adjunction