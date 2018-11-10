-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.natural_transformation
import category_theory.opposites
import category_theory.types

import category_theory.tactics.obviously

open category_theory

namespace category_theory.adjunctions

universes u₁ v₁ u₂ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

-- TODO think again about whether we should specify the conditions here in terms of natural transformations or components
structure Adjunction (L : C ⥤ D) (R : D ⥤ C) :=
  (unit       : functor.id _ ⟹ (L ⋙ R))
  (counit     : (R ⋙ L) ⟹ functor.id _)
  (triangle_1 : ∀ X : D, (unit.app (R.obj X)) ≫ (R.map (counit.app X)) = 𝟙 (R.obj X))
  (triangle_2 : ∀ X : C, (L.map (unit.app X)) ≫ (counit.app (L.obj X)) = 𝟙 (L.obj X))
  -- (Triangle_1 : (whisker_left R unit) ⊟ (whisker_right counit R) = 1) -- we'd need unitors and associators here


attribute [simp,search] Adjunction.triangle_1 Adjunction.triangle_2

infix ` ⊣ `:50 := Adjunction

@[extensionality] lemma Adjunctions_pointwise_equal
  (L : C ⥤ D) (R : D ⥤ C) (A B : L ⊣ R)
  (w1 : A.unit = B.unit) (w2 : A.counit = B.counit) : A = B :=
  begin
    induction A,
    induction B,
    tidy
  end

-- PROJECT: from an adjunction construct the triangles as equations between natural transformations.
-- def Triangle_1
--   {C D : Category}
--   {L : Functor C D}
--   {R : Functor D C}
--   (unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R))
--   (counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D)) :=
--   @vertical_composition_of_NaturalTransformations D C R (FunctorComposition (FunctorComposition R L) R) R ⟦ whisker_left R unit ⟧ ⟦ whisker_right counit R ⟧
--   = IdentityNaturalTransformation R

-- def Triangle_2
--   {C D : Category}
--   {L : Functor C D}
--   {R : Functor D C}
--   (unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R))
--   (counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D)) :=
--   @vertical_composition_of_NaturalTransformations C D L (FunctorComposition (FunctorComposition L R) L) L ⟦ whisker_right unit L ⟧ ⟦ whisker_left L counit ⟧
--   = IdentityNaturalTransformation L

@[simp,search] lemma Adjunction.unit_naturality {L : C ⥤ D} {R : D ⥤ C} (A : L ⊣ R) {X Y : C} (f : X ⟶ Y) : (A.unit.app X) ≫ (R.map (L.map f)) = f ≫ (A.unit.app Y) :=
by obviously

@[simp,search] lemma Adjunction.counit_naturality {L : C ⥤ D} {R : D ⥤ C} (A : L ⊣ R) {X Y : D} (f : X ⟶ Y) : (L.map (R.map f)) ≫ (A.counit.app Y) = (A.counit.app X) ≫ f :=
by obviously

-- PROJECT examples
-- PROJECT existence in terms of initial objects in comma categories
-- PROJECT adjoints for functors between functor categories
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end category_theory.adjunctions