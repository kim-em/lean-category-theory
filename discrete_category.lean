-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

namespace tqft.categories

definition DiscreteCategory ( α : Type ) [ d : decidable_eq α ] : Category :=
{
  Obj      := α,
  Hom      := λ X Y, if X = Y then unit else empty,
  identity := λ X, begin simp, exact () end, -- TODO how do we do this without going into tactic mode?
  compose  := λ _ _ _ _ _, sorry,
  left_identity  := sorry,
  right_identity := sorry,
  associativity  := sorry
}

end tqft.categories
