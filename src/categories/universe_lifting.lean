-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.equivalence

open categories.functor
open categories.equivalence

namespace categories

universes u₁

variable (C : Type u₁)
variable [small_category C]

instance universe_lift : large_category (ulift.{(u₁+1)} C) := 
{ Hom := λ X Y, (X.down ⟶ Y.down),
  identity := λ X, 𝟙 X.down,
  compose := λ _ _ _ f g, f ≫ g }

local attribute [applicable] uv_category.identity

definition universe_lift.equivalence : Equivalence C (ulift.{(u₁+1)} C) := by obviously

end categories