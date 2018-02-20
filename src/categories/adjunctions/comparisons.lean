-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..adjunctions
import .hom_adjunction

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.opposites
open categories.isomorphism
open categories.types

namespace categories.adjunctions

universes u

variable {C : Type (u+1)}
variable [category C]
variable {D : Type (u+1)}
variable [category D]

private definition Adjunction_to_HomAdjunction_morphism {L : Functor C D} {R : Functor D C} (A : Adjunction L R) 
  : NaturalTransformation (FunctorComposition (OppositeFunctor L × IdentityFunctor D) (HomPairing D))
                          (FunctorComposition (IdentityFunctor (Cᵒᵖ) × R) (HomPairing C)) := 
{
  components := λ P, 
    -- We need to construct the map from D.Hom (L P.1) P.2 to C.Hom P.1 (R P.2)
    λ f, (A.unit.components P.1) ≫ (R.onMorphisms f)
}

private definition Adjunction_to_HomAdjunction_inverse {L : Functor C D} {R : Functor D C} (A : Adjunction L R) 
  : NaturalTransformation (FunctorComposition (IdentityFunctor (Cᵒᵖ) × R) (HomPairing C))
                          (FunctorComposition (OppositeFunctor L × IdentityFunctor D) (HomPairing D)) :=
{
  components := λ P, 
    -- We need to construct the map back to D.Hom (L P.1) P.2 from C.Hom P.1 (R P.2)
    λ f, (L.onMorphisms f) ≫ (A.counit.components P.2)
}

definition Adjunction_to_HomAdjunction  {L : Functor C D} {R : Functor D C} (A : Adjunction L R) : HomAdjunction L R := 
{
    morphism  := Adjunction_to_HomAdjunction_morphism A,
    inverse   := Adjunction_to_HomAdjunction_inverse A
 }

@[simp] lemma mate_of_L
  {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R)
  {X Y : C} (f : Hom X Y)
    : (((A.morphism).components (X, L.onObjects X)) (𝟙 (L.onObjects X))) ≫ 
      (R.onMorphisms (L.onMorphisms f))
      = ((A.morphism).components (X, L.onObjects Y)) (L.onMorphisms f) :=
begin
  have p := @NaturalTransformation.naturality _ _ _ _ _ _ A.morphism (X, L X) (X, L Y) (𝟙 X, L.onMorphisms f),
  have q := congr_fun p (L.onMorphisms (𝟙 X)),
  tidy,
end

@[simp] lemma mate_of_L'
  {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R)
  {X Y : C} (f : Hom X Y)
    : f ≫ (((A.morphism).components (Y, L.onObjects Y)) (𝟙 (L.onObjects Y)))
      = ((A.morphism).components (X, L.onObjects Y)) (L.onMorphisms f) :=
begin
  have p := @NaturalTransformation.naturality _ _ _ _ _ _ A.morphism (Y, L.onObjects Y) (X, L.onObjects Y) (f, 𝟙 (L.onObjects Y)),
  have q := congr_fun p (L.onMorphisms (𝟙 Y)),
  tidy,
end

@[simp] lemma mate_of_R
  {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R)
  {X Y : D} (f : Hom X Y)
    : (L.onMorphisms (R.onMorphisms f)) ≫ (((A.inverse).components (R.onObjects Y, Y)) (𝟙 (R.onObjects Y)))
      = ((A.inverse).components (R.onObjects X, Y)) (R.onMorphisms f) :=
begin
  have p := @NaturalTransformation.naturality _ _ _ _ _ _ A.inverse (R.onObjects Y, Y) (R.onObjects X, Y) (R.onMorphisms f, 𝟙 Y),
  have q := congr_fun p (R.onMorphisms (𝟙 Y)),
  tidy,
end

@[simp] lemma mate_of_R'
  {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R)
  {X Y : D} (f : Hom X Y)
    : (((A.inverse).components (R.onObjects X, X)) (𝟙 (R.onObjects X))) ≫ f = 
    ((A.inverse).components (R.onObjects X, Y)) (R.onMorphisms f) :=
begin
  have p := @NaturalTransformation.naturality _ _ _ _ _ _ A.inverse (R.onObjects X, X) (R.onObjects X, Y) (𝟙 (R.onObjects X), f),
  have q := congr_fun p (R.onMorphisms (𝟙 X)),
  tidy,
end

private definition unit_from_HomAdjunction {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R) : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) := {
    components := λ X : C, (A.morphism.components (X, L.onObjects X)) (𝟙 (L.onObjects X))
 }
private definition counit_from_HomAdjunction {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R) : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) := {
    components := λ X : D, (A.inverse.components (R.onObjects X, X)) (𝟙 (R.onObjects X))
 }

-- lemma pre_triangle_1 
-- {C D : Category} {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R)
-- (X : C.Obj)
-- (Y : D.Obj)
-- : ∀ f : C.Hom X (R.onObjects Y), C.compose f (C.compose ((unit_from_HomAdjunction A).components (R.onObjects Y)) (R.onMorphisms ((counit_from_HomAdjunction A).components Y))) = f :=
-- begin
--   intro f,
--   rewrite ← C.associativity,
--   erewrite (unit_from_HomAdjunction A).naturality,
--   rewrite C.associativity,
--   tidy,
--   have p1 := A.witness_2,
--   tidy,
--   have p2 := congr_arg NaturalTransformation.components p1,
--   tidy,
--   have p3 := congr_fun p2 (X, Y),
--   tidy,
--   have p4 := congr_fun p3 f,
--   clear p1 p2 p3,
--   tidy,
-- end

-- definition HomAdjunction_to_Adjunction {C D : Category} {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R) : Adjunction L R := 
-- {
--   unit       := unit_from_HomAdjunction A,
--   counit     := counit_from_HomAdjunction A,
--   triangle_1 := begin
--                   tidy,
--                   have p1 := A.witness_2,
--                   have p2 := congr_arg NaturalTransformation.components p1,
--                   have p3 := congr_fun p2 (R.onObjects X, L.onObjects(R.onObjects X)),
--                   tidy,
--                   have p4 := congr_fun p3 (C.identity (R.onObjects X)),
--                   tidy,
--                   sorry
--                 end,
--   triangle_2 := sorry
--}

-- definition Adjunctions_agree {C D : Category} (L : Functor C D) (R : Functor D C) :
--   Isomorphism CategoryOfTypes (Adjunction L R) (HomAdjunction L R) := 
-- {
--   morphism  := Adjunction_to_HomAdjunction,
--   inverse   := HomAdjunction_to_Adjunction,
--   witness_1 := begin tidy, end,
--   witness_2 := begin
--                  tidy,
--                  -- this is just another lemma about mates; perhaps the same as the one we use above.
--                end
--}

end categories.adjunctions