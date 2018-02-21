-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..natural_transformation
import ..opposites
import ..types
import tidy.its

open categories
open categories.functor
open categories.natural_transformation
open categories.types

namespace categories.adjunctions

universes u₁ u₂

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

-- TODO think again about whether we should specify the conditions here in terms of natural transformations or components
structure Adjunction (L : Functor C D) (R : Functor D C) :=
  (unit       : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R))
  (counit     : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D))
  (triangle_1 : ∀ X : D, (unit.components (R X)) ≫ (R.onMorphisms (counit.components X)) = 𝟙 (R X)) -- FIXME why can't we use notation here?
  (triangle_2 : ∀ X : C, (L &> (unit.components X)) ≫ (counit.components (L X)) = 𝟙 (L X))

attribute [simp,ematch] Adjunction.triangle_1 Adjunction.triangle_2

@[applicable] lemma Adjunctions_pointwise_equal
  (L : Functor C D) (R : Functor D C)
  (A B : Adjunction L R)
  (w1 : A.unit = B.unit) (w2 : A.counit = B.counit) : A = B :=
  begin
    induction A,
    induction B,
    tidy
  end

-- PROJECT: from an adjunction construct the triangles as equations between natural transformations.
-- definition Triangle_1
--   {C D : Category}
--   {L : Functor C D}
--   {R : Functor D C}
--   (unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R))
--   (counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D)) :=
--   @vertical_composition_of_NaturalTransformations D C R (FunctorComposition (FunctorComposition R L) R) R ⟦ whisker_on_left R unit ⟧ ⟦ whisker_on_right counit R ⟧
--   = IdentityNaturalTransformation R

-- definition Triangle_2
--   {C D : Category}
--   {L : Functor C D}
--   {R : Functor D C}
--   (unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R))
--   (counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D)) :=
--   @vertical_composition_of_NaturalTransformations C D L (FunctorComposition (FunctorComposition L R) L) L ⟦ whisker_on_right unit L ⟧ ⟦ whisker_on_left L counit ⟧
--   = IdentityNaturalTransformation L

-- TODO automation
@[simp,ematch] lemma Adjunction.unit_naturality
  {L : Functor C D} {R : Functor D C} 
  (A : Adjunction L R) 
  {X Y : C} (f : Hom X Y) : (A.unit.components X) ≫ (R.onMorphisms (L &> f)) = f ≫ (A.unit.components Y) := -- FIXME failed notation here?
  begin
  tidy,
  erw A.unit.naturality,
  tidy,
  end

@[simp,ematch] lemma Adjunction.counit_naturality
  {L : Functor C D} {R : Functor D C} 
  (A : Adjunction L R) 
  {X Y : D} (f : Hom X Y) : (L &> (R &> f)) ≫ (A.counit.components Y) = (A.counit.components X) ≫ f :=
  begin
  tidy,
  erw A.counit.naturality,
  tidy,
  end

-- PROJECT examples
-- PROJECT existence in terms of initial objects in comma categories
-- PROJECT adjoints for functors between functor categories
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end categories.adjunctions