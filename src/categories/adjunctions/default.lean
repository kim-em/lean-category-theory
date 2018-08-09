-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.natural_transformation
import categories.opposites
import categories.types

open category_theory

namespace category_theory.adjunctions

universes u₁ u₂

variable {C : Type (u₁+1)}
variable [large_category C]
variable {D : Type (u₂+1)}
variable [large_category D]

-- TODO think again about whether we should specify the conditions here in terms of natural transformations or components
structure Adjunction (L : C ↝ D) (R : D ↝ C) :=
  (unit       : functor.id _ ⟹ (L ⋙ R))
  (counit     : (R ⋙ L) ⟹ functor.id _)
  (triangle_1 : ∀ X : D, (unit (R X)) ≫ (R.map (counit X)) = 𝟙 (R X))
  (triangle_2 : ∀ X : C, (L.map (unit X)) ≫ (counit (L X)) = 𝟙 (L X))
  -- (Triangle_1 : (whisker_on_left R unit) ⊟ (whisker_on_right counit R) = 1) -- we'd need unitors and associators here


attribute [simp,ematch] Adjunction.triangle_1 Adjunction.triangle_2

infix ` ⊣ `:50 := Adjunction

@[extensionality] lemma Adjunctions_pointwise_equal
  (L : C ↝ D) (R : D ↝ C) (A B : L ⊣ R) 
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

@[simp,ematch] lemma Adjunction.unit_naturality {L : C ↝ D} {R : D ↝ C} (A : L ⊣ R) {X Y : C} (f : X ⟶ Y) : (A.unit X) ≫ (R.map (L.map f)) = f ≫ (A.unit Y) := 
begin
  have := A.unit.naturality,
  obviously,
end

@[simp,ematch] lemma Adjunction.counit_naturality {L : C ↝ D} {R : D ↝ C} (A : L ⊣ R) {X Y : D} (f : X ⟶ Y) : (L.map (R.map f)) ≫ (A.counit Y) = (A.counit X) ≫ f :=
begin
  have := A.counit.naturality,
  obviously,
end

-- PROJECT examples
-- PROJECT existence in terms of initial objects in comma categories
-- PROJECT adjoints for functors between functor categories
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end category_theory.adjunctions