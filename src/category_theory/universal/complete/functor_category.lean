-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.currying
import category_theory.products.switch
import category_theory.functor_categories.whiskering
import category_theory.universal.complete
import category_theory.universal.complete.lemmas.cones_in_functor_categories

open category_theory
open category_theory.prod

namespace category_theory.universal

universes u v

variables {J : Type v} [small_category J] {C : Type v} [small_category C] {D : Type u} [category.{u v} D]

def switch_curry : (J ↝ (C ↝ D)) ↝ (C ↝ (J ↝ D)) := uncurry ⋙ (whisker_on_left_functor (switch C J) D) ⋙ curry

def limit_object_in_functor_category [has_limits.{u v} D] (F : J ↝ (C ↝ D)) : C ↝ D := 
(switch_curry.obj F) ⋙ functorial_limit

def limit_cone_in_functor_category [has_limits.{u v} D] (F : J ↝ (C ↝ D)) : cone F := 
{ X := limit_object_in_functor_category F,
  π := λ j, sorry,
  w := sorry }

instance [cmp : has_limits.{u v} D] : has_limits.{(max u v) v} (C ↝ D) := 
{ limit := λ J _ F, begin resetI, exact @limit_cone_in_functor_category J _ C _ D _ _ F end,
  is_limit := sorry
}

end category_theory.universal