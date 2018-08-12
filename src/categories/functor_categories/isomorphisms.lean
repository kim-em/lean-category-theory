-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.natural_isomorphism

open category_theory

namespace category_theory.functor

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ 

variable {B : Type u₁}
variable [ℬ : category.{u₁ v₁} B]
variable {C : Type u₂}
variable [𝒞 : category.{u₂ v₂} C]
include ℬ 𝒞

local attribute [backwards] category.id -- This says that whenever there is a goal of the form (X ⟶ X), we can safely complete it with the identity morphism. This isn't universally true.

def left_unitor (F : B ↝ C) : ((functor.id _) ⋙ F) ⇔ F := by obviously

def right_unitor (F : B ↝ C) : (F ⋙ (functor.id _)) ⇔ F := by obviously

variable {D : Type u₃}
variable [𝒟 : category.{u₃ v₃} D]
variable {E : Type u₄}
variable [ℰ : category.{u₄ v₄} E]
include 𝒟 ℰ 

def associator (F : B ↝ C) (G : C ↝ D) (H : D ↝ E) : ((F ⋙ G) ⋙ H) ⇔ (F ⋙ (G ⋙ H)) := by obviously 

-- PROJECT pentagon

end category_theory.functor
