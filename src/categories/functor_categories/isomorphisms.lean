-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.natural_isomorphism

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ 

variable {B : Type u₁}
variable [ℬ : category.{u₁ v₁} B]
variable {C : Type u₂}
variable [𝒞 : category.{u₂ v₂} C]
variable {D : Type u₃}
variable [𝒟 : category.{u₃ v₃} D]
variable {E : Type u₄}
variable [ℰ : category.{u₄ v₄} E]
include ℬ 𝒞 𝒟 ℰ 

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition FunctorComposition_left_unitor (F : C ↝ D) : (1 ⋙ F) ⇔ F := by obviously

definition FunctorComposition_right_unitor (F : C ↝ D) : (F ⋙ 1) ⇔ F := by obviously

definition FunctorComposition_associator (F : B ↝ C) (G : C ↝ D) (H : D ↝ E) : ((F ⋙ G) ⋙ H) ⇔ (F ⋙ (G ⋙ H)) := by obviously 

-- PROJECT pentagon

end categories.functor_categories
