-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

namespace tqft.categories

universe variables u v
open plift -- we first plift propositional equality to Type 0,
open ulift -- then ulift up to Type v

@[unfoldable] definition DiscreteCategory ( α : Type u ) : Category.{u v} :=
{
  Obj      := α,
  Hom      := λ X Y, ulift (plift (X = Y)),
  identity := λ X, up (up rfl),
  compose  := λ X Y Z f g, up (up (eq.trans (down (down f)) (down (down g)))),
  left_identity  := begin intros, induction f with f', induction f', trivial end,
  right_identity := begin intros, induction f with f', induction f', trivial end,
  associativity  := begin intros, trivial end
}

end tqft.categories
