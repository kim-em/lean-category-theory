-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category

namespace tqft.categories.examples.types

open tqft.categories

universe variables u

@[reducible] definition CategoryOfTypes : Category :=
{
    Obj := Type u,
    Hom := λ a b, a → b,

    identity := λ a, id,
    compose  := λ _ _ _ f g, g ∘ f,

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

end tqft.categories.examples.types
