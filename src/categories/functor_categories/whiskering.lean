-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.functor_categories

open categories
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ v₁ u₂ v₂ u₃ v₃

section
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C] (D : Type u₂) [𝒟 : category.{u₂ v₂} D] (E : Type u₃) [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

definition whiskering_on_left : (C ↝ D) ↝ ((D ↝ E) ↝ (C ↝ E)) := 
{ onObjects     := λ F, 
    { onObjects     := λ G, F ⋙ G,
      onMorphisms   := λ _ _ α, 1 ◫ α },
  onMorphisms   := λ F G τ, 
    { components := λ H, { components := λ c, H &> (τ.components c) } } }

definition whiskering_on_right : (D ↝ E) ↝ ((C ↝ D) ↝ (C ↝ E)) :=
{ onObjects     := λ H, 
    { onObjects     := λ F, F ⋙ H,
      onMorphisms   := λ _ _ α, α ◫ 1, },
  onMorphisms   := λ G H τ, 
    { components := λ F, { components := λ c, τ.components (F +> c) } } }
end

definition whisker_on_left_functor {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] (F : C ↝ D) (E : Type u₃) [ℰ : category.{u₃ v₃} E] : 
    (D ↝ E) ↝ (C ↝ E) :=
  (whiskering_on_left C D E) +> F

definition whisker_on_right_functor (C : Type u₁) [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] {E : Type u₃} [ℰ : category.{u₃ v₃} E](H : D ↝ E) :
  (C ↝ D) ↝ (C ↝ E) :=
(whiskering_on_right C D E) +> H

end categories.functor_categories