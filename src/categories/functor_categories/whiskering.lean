-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.functor_categories

open categories
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ u₂ u₃

section
variables (C : Type (u₁+1)) [large_category C] (D : Type (u₂+1)) [large_category D] (E : Type (u₃+1)) [large_category E]

definition whiskering_on_left : (C ↝ D) ↝ ((D ↝ E) ↝ (C ↝ E)) := {
  onObjects     := λ F, {
    onObjects     := λ G, F ⋙ G,
    onMorphisms   := λ _ _ α, 1 ◫ α 
 },
  onMorphisms   := λ F G τ, {
    components := λ H, {
      components := λ c, H &> (τ.components c)
   }
 }
}

definition whiskering_on_right : (D ↝ E) ↝ ((C ↝ D) ↝ (C ↝ E)) :=
{
  onObjects     := λ H, {
    onObjects     := λ F, F ⋙ H,
    onMorphisms   := λ _ _ α, α ◫ 1,
 },
  onMorphisms   := λ G H τ, {
    components := λ F, {
      components := λ c, τ.components (F +> c)
   }
 }
}

definition whisker_on_left_functor {C : Type (u₁+1)} [large_category C] {D : Type (u₂+1)} [large_category D] (F : C ↝ D) (E : Type (u₃+1)) [large_category E] : 
    (D ↝ E) ↝ (C ↝ E) :=
  (whiskering_on_left C D E) +> F


definition whisker_on_right_functor (C : Type (u₁+1)) [large_category C] {D : Type (u₂+1)} [large_category D] {E : Type (u₃+1)} [large_category E] (H : D ↝ E) :
  (C ↝ D) ↝ (C ↝ E) :=
(whiskering_on_right C D E) +> H

end
end categories.functor_categories