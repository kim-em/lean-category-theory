-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.currying
import category_theory.products.switch
import category_theory.functor_categories.whiskering
import category_theory.universal.complete
import category_theory.universal.complete.lemmas.cones_in_functor_categories
import category_theory.universal.comparisons

open category_theory
open category_theory.prod

namespace category_theory.universal

universes u v

private meta def dsimp' : tactic unit := `[dsimp at * {unfold_reducible := tt, md := semireducible}]

variables {J : Type v} [small_category J] {C : Type v} [small_category C] {D : Type u} [𝒟 : category.{u v} D]
include 𝒟 

def switch_curry : (J ↝ (C ↝ D)) ↝ (C ↝ (J ↝ D)) := uncurry ⋙ (whisker_on_left_functor (switch C J) D) ⋙ curry

def switched (F : J ↝ (C ↝ D)) : C ↝ (J ↝ D):= ((switch_curry : (J ↝ (C ↝ D)) ↝ (C ↝ (J ↝ D))) F)

def introduce_switch (F : J ↝ (C ↝ D)) {j j' : J} (f : j ⟶ j') (X : C) : (F.map f) X = ((switched F) X).map f := 
begin
  dunfold switched,
  dunfold switch_curry,
  dunfold curry, dunfold uncurry,
  dunfold whisker_on_left_functor,
  dunfold whiskering_on_left,
  dunfold switch,
  dsimp,
  simp,
end

def limit_cone_in_functor_category [has_limits.{u v} D] (F : J ↝ (C ↝ D)) : cone F := 
{ X := ((switched F) ⋙ functorial_limit),
  π := λ j, { app := λ X : C, (limit.cone (switched F X)).π j },
  w := begin intros j j' f, ext1, dsimp at *, rw introduce_switch, obviously, end }.

instance [has_limits.{u v} D] : has_limits.{(max u v) v} (C ↝ D) := 
{ limit := λ J _ F, begin resetI, exact limit_cone_in_functor_category F end,
  is_limit := begin 
                intros,
                apply is_limit.of_comparison,
                intros,
                dunfold limit_cone_in_functor_category,
                dunfold limit_comparison,
                dsimp,
                obviously,
                    -- obviously,
                    -- tactic.rotate_left 2,
                    -- dunfold limit_cone_in_functor_category, dsimp,
                    -- dunfold functorial_limit, dsimp,
                    -- apply limit.hom,
                    -- tactic.rotate_left 1,
                    -- resetI,
                    -- intro j,
                    -- exact (s.π j) X,
                    -- obviously,
                    -- dunfold limit.hom,
                    -- dunfold limit_cone_in_functor_category,
                    -- dsimp,
                    end
}

end category_theory.universal