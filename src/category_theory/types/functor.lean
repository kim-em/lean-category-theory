-- -- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import category_theory.types
-- import category_theory.tactics.obviously

-- open category_theory

-- universes u v

-- instance functor_of_functor (F : (Type u) ⥤ (Type v)) : _root_.functor F.obj := 
-- { map := λ _ _ f, F.map f }

-- -- local attribute [tidy] dsimp'

-- -- TODO yuck, automate
-- instance lawful_functor_of_Functor (F : (Type u) ⥤ (Type v)) : is_lawful_functor (F.obj) := 
-- { id_map := begin obviously,  end,
--   comp_map := begin
--                 tidy,
--                 calc (F.map (λ (x : α), h (g x))) x = (F.map (g ≫ h)) x      : by obviously
--                                                 ... = (F.map h) ((F.map g) x) : by obviously
--               end
-- }

-- attribute [search] is_lawful_functor.comp_map

-- def functor_of_functor' (g : Type u → Type v) [functor g] [is_lawful_functor g] : (Type u) ⥤ (Type v) := 
-- { obj := g,
--   map' := λ X Y f z, f <$> z }