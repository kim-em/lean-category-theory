-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.natural_transformation
import categories.products

open categories
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ v₁ u₂ v₂

variable (C : Type u₁)
variable [𝒞 : uv_category.{u₁ v₁} C]
variable (D : Type u₂)
variable [𝒟 : uv_category.{u₂ v₂} D]
include 𝒞 𝒟 

-- TODO remove, unnecessary
-- instance : uv_category.{(max u₁ v₁ u₂ v₂) (max u₁ v₁ v₂)} (let E := (C ↝ D) × C in E) := products.ProductCategory.{(max u₁ v₁ u₂ v₂) (max u₁ v₂) u₁ v₁} (C ↝ D) C

definition Evaluation : ((C ↝ D) × C) ↝ D := {
  onObjects     := λ p, p.1 +> p.2,
  onMorphisms   := λ x y f, (x.1 &> f.2) ≫ (f.1.components y.2)
}

end categories.functor_categories