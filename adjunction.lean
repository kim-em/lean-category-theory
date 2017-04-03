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
  ( unit   : NaturalTransformation (IdentityFunctor D) (FunctorComposition R L) )
  ( counit : NaturalTransformation (FunctorComposition L R) (IdentityFunctor C) ) :=
  @vertical_composition_of_NaturalTransformations C D L (FunctorComposition (FunctorComposition L R) L) L ⟦ whisker_on_left L unit ⟧ ⟦ whisker_on_right counit L ⟧
  = IdentityNaturalTransformation L

@[reducible] definition Triangle_2
  { C D : Category }
  { L : Functor C D }
  { R : Functor D C }
  ( unit   : NaturalTransformation (IdentityFunctor D) (FunctorComposition R L) )
  ( counit : NaturalTransformation (FunctorComposition L R) (IdentityFunctor C) ) :=
  @vertical_composition_of_NaturalTransformations D C R (FunctorComposition (FunctorComposition R L) R) R ⟦ whisker_on_right unit R ⟧ ⟦ whisker_on_left R counit ⟧
  = IdentityNaturalTransformation R

structure Adjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  ( unit          : NaturalTransformation (IdentityFunctor D) (FunctorComposition R L) )
  ( counit        : NaturalTransformation (FunctorComposition L R) (IdentityFunctor C) )
  ( triangle_1    : Triangle_1 unit counit )
  ( triangle_2    : Triangle_2 unit counit )

local attribute [pointwise] funext

definition { u v } HomPairing ( C : Category.{u v} ) : Functor ((Opposite C) × C) CategoryOfTypes.{v} :=
{
  onObjects     := λ p, C.Hom p.1 p.2,
  onMorphisms   := λ X F f, λ g, C.compose (C.compose f.1 g) f.2,
  identities    := begin blast, rewrite C.left_identity end, -- FIXME why doesn't blast work?
  functoriality := ♯
}

definition HomAdjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  NaturalIsomorphism
    (FunctorComposition (OppositeFunctor L × IdentityFunctor D) (HomPairing D))
    (FunctorComposition (IdentityFunctor (Opposite C) × R) (HomPairing C))

definition Adjunctions_agree { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :
  Isomorphism CategoryOfTypes (Adjunction L R) (HomAdjunction L R) := sorry -- PROJECT

-- PROJECT examples
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end tqft.categories.adjunction