-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.products
import categories.natural_isomorphism
import category_theory.opposites
import categories.isomorphism

open category_theory

namespace category_theory.adjunctions

universes u₁ v₁

-- TODO should we allow different universe levels, at the expense of some lifts?
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₁} [𝒟 : category.{u₁ v₁} D]
include 𝒞 𝒟 

def hom_adjunction (L : C ↝ D) (R : D ↝ C) :=
    ((functor.prod L.opposite (functor.id D)) ⋙ (hom_pairing D))
      ⇔ 
    (functor.prod (functor.id (Cᵒᵖ)) R) ⋙ (hom_pairing C)

def mate {L : C ↝ D} {R : D ↝ C} (A : hom_adjunction L R) {X : C} {Y : D} (f : (L X) ⟶ Y) : X ⟶ (R Y)
  := ((A.hom) (X, Y)) f

-- PROJECT lemmas about mates.

-- PROJECT -- to do this, we need to first define whiskering of NaturalIsomorphisms
-- See Remark 2.1.11 of Leinster
-- def composition_of_HomAdjunctions
--   {C D E : Category} {L : Functor C D} {L' : Functor D E} {R : Functor D C} {R' : Functor E D}
--   (A : HomAdjunction L R) (B : HomAdjunction L' R')
--     : HomAdjunction (FunctorComposition L L') (FunctorComposition R' R) := sorry

end category_theory.adjunctions