-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

namespace tqft.categories

-- TODO extending Category to work with Sort breaks other things.

-- definition DiscreteCategory ( α : Type ) : Category :=
-- {
--   Obj      := α,
--   Hom      := λ X Y, X = Y,
--   identity := λ X, rfl,
--   compose  := λ X Y Z f g, eq.trans f g,
--   left_identity  := ♮,
--   right_identity := ♮,
--   associativity  := ♮
-- }
definition DiscreteCategory ( α : Type ) : Category :=
{
  Obj      := α,
  Hom      := λ X Y, sorry,
  identity := λ X, sorry,
  compose  := λ X Y Z f g, sorry,
  left_identity  := sorry,
  right_identity := sorry,
  associativity  := sorry
}

end tqft.categories
