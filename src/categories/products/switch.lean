-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.products
import categories.natural_isomorphism

open category_theory

namespace category_theory.prod

universes u₁ v₁ u₂ v₂ 

local attribute [back] category.id -- This says that whenever there is a goal of the form `X ⟶ X`, we can safely complete it with the identity morphism. This isn't universally true.

variable (C : Type u₁)
variable [𝒞 : category.{u₁ v₁} C]
variable (D : Type u₂)
variable [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

def switch : (C × D) ↝ (D × C) :=
{ obj := λ X, (X.2, X.1),
  map := λ _ _ f, (f.2, f.1) }

def symmetry : ((switch C D) ⋙ (switch D C)) ⇔ (functor.id (C × D)) := by obviously
        
end category_theory.prod
