-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.currying.currying_2
import categories.equivalence

open categories
open categories.isomorphism
open categories.functor
open categories.equivalence
open categories.functor_categories

namespace categories.natural_transformation

universes u₁ u₂ v₂ 

variables (C : Type u₁) [small_category C] (D : Type u₁) [small_category D] (E : Type u₂) [ℰ : category.{u₂ v₂} E]
include ℰ

local attribute [tidy] dsimp_all'

theorem Currying_for_functors :
  Equivalence (C ↝ (D ↝ E)) ((C × D) ↝ E) := 
  {
    functor := Uncurry_Functors C D E,
    inverse := Curry_Functors C D E,
    isomorphism_1 := {
     morphism  := Curry_Uncurry_to_identity C D E,
     inverse   := identity_to_Curry_Uncurry C D E
   },
    isomorphism_2 := {
     morphism  := Uncurry_Curry_to_identity C D E,
     inverse   := identity_to_Uncurry_Curry C D E
   },
 }

end categories.natural_transformation