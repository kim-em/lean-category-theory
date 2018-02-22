-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products
import ..natural_isomorphism

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

universes u₁ u₂ 

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

variable (C : Type (u₁+1))
variable [category C]
variable (D : Type (u₂+1))
variable [category D]

definition SwitchProductCategory : (C × D) ↝ (D × C) :=
{
  onObjects     := λ X, (X.2, X.1),
  onMorphisms   := λ _ _ f, (f.2, f.1)
}

definition SwitchSymmetry : ((SwitchProductCategory C D) ⋙ (SwitchProductCategory D C)) ⇔ 1 := ♯
        
end categories.products
