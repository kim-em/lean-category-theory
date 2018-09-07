-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.currying
import category_theory.functor_categories.whiskering
import category_theory.universal.comparisons

open category_theory
open category_theory.prod

namespace category_theory.limits

universes u v

-- private meta def dsimp' : tactic unit := `[dsimp at * {unfold_reducible := tt, md := semireducible}]

variables {J : Type v} [small_category J] {C : Type v} [small_category C] {D : Type u} [𝒟 : category.{u v} D]
include 𝒟 

def switched (F : J ⥤ (C ⥤ D)) : C ⥤ (J ⥤ D) :=
{ obj := λ c, { obj := λ j, (F j) c, map' := λ j j' f, (F.map f) c },
  map' := λ c c' f, { app := λ j, (F j).map f }}.

-- section
-- local attribute [back] category.id
-- def switched_twice (F : J ⥤ (C ⥤ D)) : switched (switched F) ≅ F := by obviously
-- end

def introduce_switch (F : J ⥤ (C ⥤ D)) {j j' : J} (f : j ⟶ j') (X : C) : (F.map f) X = ((switched F) X).map f := sorry


def limit_cone_in_functor_category [has_limits.{u v} D] (F : J ⥤ (C ⥤ D)) : cone F := 
{ X := ((switched F) ⋙ lim),
  π := λ j, { app := λ X : C, (limit.cone (switched F X)).π j },
  w := λ j j' f, begin ext1, dsimp at *, rw introduce_switch, obviously, end }.

instance [has_limits.{u v} D] : has_limits.{(max u v) v} (C ⥤ D) := 
{ limit := λ J 𝒥 F, begin resetI, exact limit_cone_in_functor_category F end,
  is_limit := λ J 𝒥 F, begin resetI, exact
  { lift := λ s, { app := λ X, (limit.cone_morphism (switched F X) { X := s.X X, π := λ j, (s.π j) X }).hom,
                   naturality' := begin tidy, dsimp [limit_cone_in_functor_category],
                  -- FIXME why does this rw fail? I wanted to apply this to both sides, then use naturality.
                  --  rw limit.pullback_lift (switched F Y),
                  sorry
                    end, },
    fac' := sorry,
    uniq' := sorry } end
}

end category_theory.limits