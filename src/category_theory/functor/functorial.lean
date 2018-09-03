-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison


import category_theory.functor
import category_theory.tactics.obviously

namespace category_theory

universes u₁ u₂

variable {C : Type (u₁+1)}
variable [large_category C]
variable {D : Type (u₂+1)}
variable [large_category D]

-- TODO this is WIP
class functorial (f : C → D) :=
(map   : Π {X Y : C}, (X ⟶ Y) → ((f X) ⟶ (f Y)))
(map_id'    : ∀ (X : C), map (𝟙 X) = 𝟙 (f X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

restate_axiom functorial.map_id'
restate_axiom functorial.map_comp'
attribute [simp,search] functorial.map_comp functorial.map_id

-- instance (F : C ⥤ D) : functorial (F.obj) := 
-- { map := F.map' }

-- TODO notations?
end category_theory