-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor
import categories.isomorphism

open category_theory

namespace category_theory

universes u₁ u₂ 

variable {C : Type (u₁+1)}
variable [large_category C]
variable {D : Type (u₂+1)}
variable [large_category D]

-- Functors preserve isomorphisms
-- definition Functor.onIsomorphisms (F : C ↝ D) {X Y : C} (g : X ≅ Y) : (F +> X) ≅ (F +> Y) := {
--     morphism := F &> g.morphism,
--     inverse := F &> g.inverse,
-- }

class ReflectsIsomorphisms (F : C ↝ D) :=
  (reflects : Π {X Y : C} (f : X ⟶ Y) (w : is_Isomorphism (F &> f)), is_Isomorphism f)

end category_theory