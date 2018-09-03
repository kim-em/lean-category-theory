-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor
import category_theory.isomorphism

open category_theory

namespace category_theory

universes u₁ v₁ u₂ v₂

variables {C : Type u₁} [category.{u₁ v₁} C] {D : Type u₂} [category.{u₂ v₂} D]

class reflects_isos (F : C ↝ D) :=
(reflects : Π {X Y : C} (f : X ⟶ Y) (w : is_iso (F.map f)), is_iso f)

-- TODO
-- instance (F : C ↝ D) [faithful F] : reflects_isos F := sorry

end category_theory