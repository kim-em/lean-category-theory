-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor

namespace categories

universes u₁ u₂ 

open categories.functor

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition  DiscreteCategory (α : Type u₁) : category α := {
  Hom            := λ X Y, ulift (plift (X = Y)),
  identity       := ♯,
  compose        := ♯
}

definition EmptyCategory := DiscreteCategory (pempty.{u₁})

definition EmptyFunctor (C : Type u₂) [category C] : @Functor _ EmptyCategory.{u₁} C _ := ♯

definition {u1 v1 u2 v2} Functor.fromFunction {C : Type u₂} [category C] {I : Type u₂} (F : I → C) : @Functor _ (DiscreteCategory I) C _ := {
  onObjects     := F,
  onMorphisms   := begin tidy, induction a, induction a, induction a, tidy, end, -- FIXME this used to work by ♯
  -- identities :=sorry,
  -- functoriality:=sorry
}

end categories
