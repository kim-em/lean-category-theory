-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..natural_transformation
import ..opposites
import ..products.products
import ..isomorphism
import ..types

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.isomorphism
open tqft.categories.types

namespace tqft.categories.adjunction

structure Adjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  ( unit       : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
  ( counit     : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) )
  ( triangle_1 : ∀ X : D.Obj, C.compose (unit.components (R.onObjects X)) (R.onMorphisms (counit.components X)) = C.identity (R.onObjects X) )
  ( triangle_2 : ∀ X : C.Obj, D.compose (L.onMorphisms (unit.components X)) (counit.components (L.onObjects X)) = D.identity (L.onObjects X) )

attribute [ematch] Adjunction.triangle_1 Adjunction.triangle_2

@[pointwise] lemma Adjunctions_pointwise_equal
  { C D : Category } ( L : Functor C D ) ( R : Functor D C )
  ( A B : Adjunction L R )
  ( w1 : A.unit = B.unit ) ( w2 : A.counit = B.counit ) : A = B :=
  begin
    induction A,
    induction B,
    blast
  end

-- PROJECT: from an adjunction construct the triangles as equations between natural transformations.
-- definition Triangle_1
--   { C D : Category }
--   { L : Functor C D }
--   { R : Functor D C }
--   ( unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
--   ( counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) ) :=
--   @vertical_composition_of_NaturalTransformations D C R (FunctorComposition (FunctorComposition R L) R) R ⟦ whisker_on_left R unit ⟧ ⟦ whisker_on_right counit R ⟧
--   = IdentityNaturalTransformation R

-- definition Triangle_2
--   { C D : Category }
--   { L : Functor C D }
--   { R : Functor D C }
--   ( unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
--   ( counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) ) :=
--   @vertical_composition_of_NaturalTransformations C D L (FunctorComposition (FunctorComposition L R) L) L ⟦ whisker_on_right unit L ⟧ ⟦ whisker_on_left L counit ⟧
--   = IdentityNaturalTransformation L

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

-- PROJECT examples
-- PROJECT left adjoints preserve limits
-- PROJECT existence in terms of initial objects in comma categories
-- PROJECT adjoints for functors between functor categories
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end tqft.categories.adjunction