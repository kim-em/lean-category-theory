-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.equivalence

open categories.functor
open categories.equivalence

namespace categories

universes u₁ u₂

variable (C : Type (u₁+1))
variable [category C]

instance universe_lift : category (ulift.{(u₂+1)} C) := {
    Hom := λ X Y, ulift (X.down ⟶ Y.down),
    identity := λ X, ulift.up (𝟙 X.down),
    compose := λ _ _ _ f g, ulift.up (f.down ≫ g.down) 
}

local attribute [applicable] category.identity

definition universe_lift.equivalence : Equivalence C (ulift.{(u₂+1)} C) := by obviously

end categories