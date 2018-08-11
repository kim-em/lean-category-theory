-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.currying
import categories.products.switch
import categories.functor_categories.whiskering
import categories.universal.complete
import categories.universal.complete.lemmas.cones_in_functor_categories

open category_theory
open category_theory.prod

namespace category_theory.universal

universes j u₁ u₂
variable {J : Type u₁}
variable [small_category J]
variable {C : Type u₁}
variable [small_category C]
variable {D : Type (u₁+1)}
variable [large_category D]

definition switch_curry : (J ↝ (C ↝ D)) ↝ (C ↝ (J ↝ D)) := uncurry J C D ⋙ (whisker_on_left_functor (switch C J) D) ⋙ curry C J D

definition LimitObject_in_FunctorCategory [Complete D] (F : J ↝ (C ↝ D)) : C ↝ D := 
(switch_curry.obj F) ⋙ functorial_Limit

definition LimitCone_in_FunctorCategory [Complete D] (F : J ↝ (C ↝ D)) : Cone F := 
{ cone_point := LimitObject_in_FunctorCategory F,
  cone_maps  := λ j, sorry }

instance Limits_in_FunctorCategory [cmp : Complete D] : Complete (C ↝ D) := {
  limitCone := λ J _ F, begin
                          exact {
                            obj    := @LimitCone_in_FunctorCategory J _ C _ D _ _ F,
                            «from» := sorry
                          }
                        end
}

end category_theory.universal