-- -- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import ...adjunctions

-- open categories
-- open categories.functor
-- open categories.natural_transformation
-- open categories.products
-- open categories.isomorphism
-- open categories.types
-- open categories.functor_categories

-- namespace categories.adjunctions

-- -- EXERCISE an adjunction F ⊢ G gives an adjunction F^* ⊢ G^*
-- -- cf Leinster 2.2.14
-- -- definition pullback_adjunction {C D : Category} {L : Functor C D} {R : Functor D C} (A : Adjunction L R) (E : Category)
-- --   : Adjunction (whisker_on_left_functor E L) (whisker_on_left_functor E R) := {
-- --     unit       := sorry,
-- --     counit     := sorry,
-- --     triangle_1 := sorry,
-- --     triangle_2 := sorry
-- --  }

-- end categories.adjunctions