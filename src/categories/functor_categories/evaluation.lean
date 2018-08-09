-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.products
import ..tactics.obviously

open category_theory

namespace category_theory.FunctorCategory

universes u₁ v₁ u₂ v₂

variable (C : Type u₁)
variable [𝒞 : category.{u₁ v₁} C]
variable (D : Type u₂)
variable [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟 

definition Evaluation : ((C ↝ D) × C) ↝ D := 
{ obj := λ p, p.1 p.2,
  map := λ x y f, (x.1.map f.2) ≫ (f.1 y.2) }

end category_theory.FunctorCategory