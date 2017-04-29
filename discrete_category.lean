-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor

namespace tqft.categories

open tqft.categories.functor
open plift -- we first plift propositional equality to Type 0,
open ulift -- then ulift up to Type v

definition {u v} DiscreteCategory ( α : Type u ) : Category.{u v} :=
{
  Obj      := α,
  Hom      := λ X Y, ulift (plift (X = Y)),
  identity := λ X, up (up rfl),
  compose  := λ X Y Z f g, up (up (eq.trans (down (down f)) (down (down g)))),
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition {u v} EmptyCategory := DiscreteCategory.{u v} (ulift empty)

definition {u1 v1 u2 v2} EmptyFunctor ( C : Category.{u2 v2} ) : Functor EmptyCategory.{u1 v1} C := ♯

end tqft.categories
