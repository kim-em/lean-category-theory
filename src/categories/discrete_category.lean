-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor

namespace categories

open categories.functor
open plift -- we first plift propositional equality to Type 0,
open ulift -- then ulift up to Type v

local attribute [applicable] Category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition {u v} DiscreteCategory (α : Type u) : Category.{u v} :=
{
  Obj            := α,
  Hom            := λ X Y, ulift (plift (X = Y)),
  identity       := ♯,
  compose        := ♯
}

definition {u v} EmptyCategory := DiscreteCategory.{u v} (ulift empty)

definition {u1 v1 u2 v2} EmptyFunctor (C : Category.{u2 v2}) : Functor EmptyCategory.{u1 v1} C := ♯

open tactic

definition {u1 v1 u2 v2} Functor.fromFunction {C : Category.{u1 v1}} {I : Type u2} (F : I → C.Obj) : Functor (DiscreteCategory.{u2 v2} I) C := {
  onObjects     := F,
  onMorphisms   := ♯
}

end categories
