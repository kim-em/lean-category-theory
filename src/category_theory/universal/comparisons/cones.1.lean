-- -- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Stephen Morgan, Scott Morrison

-- import category_theory.equivalence
-- import category_theory.universal.cones
-- import category_theory.universal.comma_categories

-- open category_theory
-- open category_theory.universal
-- open category_theory.comma

-- namespace category_theory.universal

-- universes u v u₁ v₁ u₂ v₂ 
-- variables {J : Type v} [small_category J]
-- variables {C : Type u} [𝒞 : category.{u v} C]
-- include 𝒞 

-- @[simp] lemma comma.Cone.commutativity (F : J ⥤ C) (X : C) (cone : ((DiagonalFunctor J C) X) ⟶ ((ObjectAsFunctor.{(max u v) v} F).obj punit.star)) {j k : J} (f : j ⟶ k) : cone j ≫ (F.map f) = cone k := 
-- by obviously

-- local attribute [back] category.id

-- def Cones_agree (F : J ⥤ C) : Equivalence (comma.Cone F) (cone F) := 
-- { functor := { obj := λ c, { X := c.1.1,
--                              π := λ j : J, (c.2) j },
--                map' := λ X Y f, { hom := f.left } },
--   inverse := { obj := λ c, ⟨ (c.X, by obviously), { app := λ j, c.π j } ⟩,
--                map' := λ X Y f, { left := f.hom, right := by obviously } } }

-- end category_theory.universal