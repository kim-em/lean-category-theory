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

definition discrete (α : Type u₁) := α

instance  DiscreteCategory (α : Type (u₁+1)) : category (discrete α) := {
  Hom            := λ X Y, ulift (plift (X = Y)),
  identity       := ♯,
  compose        := ♯
}

instance EmptyCategory : category pempty := (by apply_instance : category (discrete pempty))
instance OneCategory : category punit := (by apply_instance : category (discrete punit))

definition EmptyFunctor (C : Type (u₂+1)) [category C] : pempty ↝ C := ♯

-- FIXME This is really horrible! Please help out. :-)
definition Functor.fromFunction {C : Type (u₂+1)} [category C] {I : Type (u₁+1)} (F : I → C) : (discrete I) ↝ C := {
  onObjects     := F,
  onMorphisms   := λ X Y f, begin cases f, cases f, rw f, exact 𝟙 (F Y) end,
  identities := begin tidy, end,
  functoriality:= begin tidy, cases f, cases f, induction f, cases g, cases g, induction g, tidy, end
}

end categories
