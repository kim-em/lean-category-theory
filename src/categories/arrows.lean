-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .functor_categories

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.arrows

universes u₁ u₂

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

-- Is there any point defining these separately (rather than as the functor category from the walking arrow)?

definition arrows (C : Type u₁) [category C] := Σ (p : C × C), Hom p.1 p.2

definition Arrows (C : Type u₁) [category C] : category (arrows C):= {
  Hom := λ X Y, {f : (Hom X.1.1 Y.1.1 × Hom X.1.2 Y.1.2) // f.1 >> Y.2 = X.2 >> f.2},
  identity       := by tidy,
  compose        := λ X Y Z f g, ⟨ (f.val.1 >> g.val.1, f.val.2 >> g.val.2), ♯ ⟩ 
}

variable {C : Type u₁}
variable [category C]
variable {D : Type u₂}
variable [category D]

definition Functor.onArrows : Functor (Functor C D) (Functor (arrows C) (arrows D)) := {
  onObjects := λ F, {
    onObjects     := λ X, ⟨ (F.onObjects X.1.1, F.onObjects X.1.2), F.onMorphisms X.2 ⟩,
    onMorphisms   := λ X Y f, ⟨ (F.onMorphisms f.val.1, F.onMorphisms f.val.2), ♯ ⟩
  },
  onMorphisms := λ F G τ, {
    components := λ X, ⟨ (τ.components X.1.1, τ.components X.1.2), ♯ ⟩ 
  }
}

end categories.arrows
