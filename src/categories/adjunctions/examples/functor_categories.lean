-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ...adjunctions

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.isomorphism
open categories.types
open categories.functor_categories

namespace categories.adjunctions

universes u₁ u₂ u₃

variable {C : Type u₁}
variable [category C]
variable {D : Type u₂}
variable [category D]
variable {E : Type u₃}
variable [category E]


-- EXERCISE an adjunction F ⊢ G gives an adjunction F^* ⊢ G^*
-- cf Leinster 2.2.14
-- definition pullback_adjunction {L : Functor C D} {R : Functor D C} (A : Adjunction L R) 
--   : Adjunction (whisker_on_left_functor L E) (whisker_on_left_functor R E) := {
--     unit       := sorry,
--     counit     := sorry,
--     triangle_1 := sorry,
--     triangle_2 := sorry
--  }

end categories.adjunctions