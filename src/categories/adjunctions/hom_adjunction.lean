-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.natural_isomorphism
import categories.opposites
import categories.products
import categories.isomorphism
import categories.types

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.isomorphism
open categories.types
open categories.opposites

namespace categories.adjunctions

universes u v

variable {C : Type u}
variable [𝒞 : uv_category.{u v} C]
variable {D : Type u}
variable [𝒟 : uv_category.{u v} D]
include 𝒞 𝒟

definition HomAdjunction (L : C ↝ D) (R : D ↝ C) :=
    ((OppositeFunctor L × IdentityFunctor D) ⋙ (HomPairing D))
      ⇔ 
    ((IdentityFunctor (Cᵒᵖ) × R) ⋙ (HomPairing C))

definition mate {L : Functor C D} {R : Functor D C} (A : HomAdjunction L R) {X : C} {Y : D} (f : (L +> X) ⟶ Y) : X ⟶ (R +> Y)
  := ((A.morphism).components (X, Y)) f

-- PROJECT lemmas about mates.

-- PROJECT -- to do this, we need to first define whiskering of NaturalIsomorphisms
-- See Remark 2.1.11 of Leinster
-- definition composition_of_HomAdjunctions
--   {C D E : Category} {L : Functor C D} {L' : Functor D E} {R : Functor D C} {R' : Functor E D}
--   (A : HomAdjunction L R) (B : HomAdjunction L' R')
--     : HomAdjunction (FunctorComposition L L') (FunctorComposition R' R) := sorry

end categories.adjunctions