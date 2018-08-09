-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor_category
import tactic.interactive
import categories.tactics.obviously

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃

section
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C] (D : Type u₂) [𝒟 : category.{u₂ v₂} D] (E : Type u₃) [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

definition whiskering_on_left : (C ↝ D) ↝ ((D ↝ E) ↝ (C ↝ E)) := 
{ obj     := λ F, 
    { obj     := λ G, F ⋙ G,
      map   := λ _ _ α, (nat_trans.id _) ◫ α },
  map   := λ F G τ, 
    { app := λ H, { app := λ c, H.map (τ c) } } }

definition whiskering_on_right : (D ↝ E) ↝ ((C ↝ D) ↝ (C ↝ E)) :=
{ obj     := λ H, 
    { obj     := λ F, F ⋙ H,
      map   := λ _ _ α, α ◫ (nat_trans.id _), },
  map   := λ G H τ, 
    { app := λ F, { app := λ c, τ (F c) } } }
end

definition whisker_on_left_functor {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] (F : C ↝ D) (E : Type u₃) [ℰ : category.{u₃ v₃} E] : 
    (D ↝ E) ↝ (C ↝ E) :=
  (whiskering_on_left C D E) F

definition whisker_on_right_functor (C : Type u₁) [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] {E : Type u₃} [ℰ : category.{u₃ v₃} E] (H : D ↝ E) :
  (C ↝ D) ↝ (C ↝ E) :=
(whiskering_on_right C D E) H

definition whisker_on_left {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] {E : Type u₃} [ℰ : category.{u₃ v₃} E]  (F : C ↝ D) {G H : D ↝ E} (α : G ⟹ H) : (F ⋙ G) ⟹ (F ⋙ H) := 
  (whisker_on_left_functor F E).map α

definition whisker_on_right {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] {E : Type u₃} [ℰ : category.{u₃ v₃} E] {G H : C ↝ D} (α : G ⟹ H)  (F : D ↝ E) : (G ⋙ F) ⟹ (H ⋙ F) := 
  (whisker_on_right_functor C F).map α

end category_theory