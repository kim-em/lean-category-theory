-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

namespace tqft.categories

open plift

definition DiscreteCategory ( α : Type ) : Category :=
{
  Obj      := α,
  Hom      := λ X Y, plift (X = Y),
  identity := λ X, up rfl,
  compose  := λ X Y Z f g, up (eq.trans (down f) (down g)),
  left_identity  := by intros; induction f; trivial,
  right_identity := by intros; induction f; trivial,
  associativity  := by intros; induction f; induction g; induction h; trivial
}

end tqft.categories
