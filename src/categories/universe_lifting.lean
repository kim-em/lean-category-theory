-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.equivalence

namespace category_theory

universes u₁

variable (C : Type u₁)
variable [small_category C]

instance universe_lift : large_category (ulift.{(u₁+1)} C) := 
{ hom  := λ X Y, (X.down ⟶ Y.down),
  id   := λ X, 𝟙 X.down,
  comp := λ _ _ _ f g, f ≫ g }

local attribute [back] category.id

def universe_lift.equivalence : Equivalence C (ulift.{(u₁+1)} C) := by obviously

end category_theory