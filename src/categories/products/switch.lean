-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.products
import categories.natural_isomorphism

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

universes u₁ v₁ u₂ v₂ 

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

variable (C : Type u₁)
variable [𝒞 : category.{u₁ v₁} C]
variable (D : Type u₂)
variable [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

definition SwitchProductCategory : (C × D) ↝ (D × C) :=
{ onObjects     := λ X, (X.2, X.1),
  onMorphisms   := λ _ _ f, (f.2, f.1) }

definition SwitchSymmetry : ((SwitchProductCategory C D) ⋙ (SwitchProductCategory D C)) ⇔ (IdentityFunctor (C × D)) := by obviously
        
end categories.products
