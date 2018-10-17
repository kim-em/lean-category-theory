-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.products.bifunctors
import category_theory.equivalence

-- FIXME why do we need this here?
@[obviously] meta def obviously_2 := tactic.tidy { tactics := extended_tidy_tactics }

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

-- FIXME this is taking too long again.

-- def uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E) :=
-- { obj := λ F, { obj := λ X, (F X.1) X.2,
--                 map' := λ X Y f, ((F.map f.1) X.2) ≫ ((F Y.1).map f.2) },
--   map' := λ F G T, { app := λ X, (T X.1) X.2 } }.

-- def curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E)) :=
-- { obj := λ F, { obj := λ X, { obj := λ Y, F (X, Y),
--                               map' := λ Y Y' g, F.map (𝟙 X, g) },
--                 map' := λ X X' f, { app := λ Y, F.map (f, 𝟙 Y) } },
--   map' := λ F G T, { app := λ X, { app := λ Y, T (X, Y) } } }.

-- -- We need the @s here in order for the coercions to work. :-(
-- @[simp] lemma uncurry.obj_map {F : C ⥤ (D ⥤ E)} {X Y : C × D} {f : X ⟶ Y} : (@uncurry C _ D _ E _ F).map f = ((F.map f.1) X.2) ≫ ((F Y.1).map f.2) := rfl
-- @[simp] lemma curry.obj_obj_map {F : (C × D) ⥤ E} {X : C} {Y Y' : D} {g : Y ⟶ Y'} : ((@curry C _ D _ E _ F) X).map g = F.map (𝟙 X, g) := rfl
-- @[simp] lemma curry.obj_map_app {F : (C × D) ⥤ E} {X X' : C} {f : X ⟶ X'} {Y} : ((@curry C _ D _ E _ F).map f) Y = F.map (f, 𝟙 Y) := rfl

-- local attribute [back] category.id -- this is usually a bad idea, but just what we needed here

-- def currying : equivalence (C ⥤ (D ⥤ E)) ((C × D) ⥤ E) :=
-- { functor := uncurry,
--   inverse := curry }

end category_theory