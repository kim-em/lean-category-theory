-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor
import tidy.its

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

-- FIXME This is really horrible! Please help out. :-)
definition {u1 v1 u2 v2} Functor.fromFunction {C : Type u₂} [category C] {I : Type u₂} (F : I → C) : @Functor _ (DiscreteCategory I) C _ := {
  onObjects     := F,
  onMorphisms   := λ X Y f, begin cases f, cases f, rw f, exact 𝟙 (F Y) end,
  identities := begin tidy, end,
  functoriality:= begin tidy, cases f, cases f, induction f, cases g, cases g, induction g, tidy, end
}

end categories
