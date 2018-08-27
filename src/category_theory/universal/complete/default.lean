-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.cones

open category_theory

namespace category_theory.universal

universes u v 

variables {C : Type u} [category.{u v} C] {J : Type v} [small_category J]

def functorial_limit [has_limits.{u v} C] : (J ↝ C) ↝ C := 
{ obj := λ F, limit F,
  map' := λ F G τ, (limit.hom G { X := _,
                                  π := (λ j, ((limit.cone F).π j) ≫ (τ j)) }).hom }.

@[simp] lemma functorial_limit_map [has_limits.{u v} C] {F G : J ↝ C} (τ : F ⟹ G) : 
  functorial_limit.map τ = (limit.hom G { X := _, π := (λ j, ((limit.cone F).π j) ≫ (τ j)) }).hom :=
rfl

-- def functorial_colimit [has_colimits C] : (J ↝ C) ↝ C := 
-- { obj := λ F, colimit F,
--   map' := λ F G τ, (colimit.hom F { X := _,
--                                     π := (λ j, (τ j) ≫ ((colimit_cocone G).π j)) }).hom }

end category_theory.universal