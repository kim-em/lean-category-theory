-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category

open tqft.categories

namespace tqft.categories.examples

definition monoid_as_category { α : Type } ( m : monoid α ) : Category :=
{
    Obj      := unit,
    Hom      := λ _ _, α,
    compose  := λ _ _ _ f g, f * g,
    identity := λ _, one,
    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

structure CategoryWithOneObject extends Category :=
  ( object  : Obj )
  ( witness : ∀ X : Obj, X = object )

end tqft.categories.examples