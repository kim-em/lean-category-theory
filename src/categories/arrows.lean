-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.natural_transformation
import categories.functor_categories

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.arrows

universes u₁ u₂

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

-- Is there any point defining these separately (rather than as the functor category from the walking arrow)?

definition arrow (C : Type (u₁+1)) [category C] := Σ (p : C × C), p.1 ⟶ p.2
structure arrow_hom {C : Type (u₁+1)} [category C] (X Y : arrow C) :=
(morphism : (X.1.1 ⟶ Y.1.1) × (X.1.2 ⟶ Y.1.2))
(commutativity : morphism.1 ≫ Y.2 = X.2 ≫ morphism.2 . obviously)

make_lemma arrow_hom.commutativity
attribute [search] arrow_hom.commutativity_lemma

@[applicable] lemma arrow_hom_equal
  {C : Type (u₁+1)} [category C] (f g : arrow C)
  (α β : arrow_hom f g)
  (w : α.morphism = β.morphism) : α = β :=
  begin
    induction α with α_morphism,
    induction β with β_morphism,
    tidy,
  end


instance Arrows (C : Type (u₁+1)) [category C] : category (arrow C):= {
  Hom := arrow_hom,
  identity       := by tidy,
  compose        := λ X Y Z f g, ⟨ (f.morphism.1 ≫ g.morphism.1, f.morphism.2 ≫ g.morphism.2) ⟩ 
}

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

definition Functor.onArrows : Functor (Functor C D) (Functor (arrow C) (arrow D)) := {
  onObjects := λ F, {
    onObjects     := λ X, ⟨ (F X.1.1, F X.1.2), F &> X.2 ⟩,
    onMorphisms   := λ X Y f, ⟨ (F &> f.morphism.1, F &> f.morphism.2) ⟩
  },
  onMorphisms := λ F G τ, {
    components := λ X, ⟨ (τ.components X.1.1, τ.components X.1.2) ⟩ 
  }
}

end categories.arrows
