-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.natural_transformation
import category_theory.functor_category
import .tactics.obviously

universes u₁ u₂

open category_theory

namespace category_theory.arrows

local attribute [back] category.id -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

-- Is there any point defining these separately (rather than as the functor category from the walking arrow)?

def arrow (C : Type (u₁+1)) [large_category C] := Σ (p : C × C), p.1 ⟶ p.2

structure arrow_hom {C : Type (u₁+1)} [large_category C] (X Y : arrow C) :=
(morphism : (X.1.1 ⟶ Y.1.1) × (X.1.2 ⟶ Y.1.2))
(commutativity : morphism.1 ≫ Y.2 = X.2 ≫ morphism.2 . obviously')

restate_axiom arrow_hom.commutativity
attribute [ematch] arrow_hom.commutativity_lemma

@[extensionality] lemma ext {C : Type (u₁+1)} [large_category C] (f g : arrow C) (α β : arrow_hom f g) (w : α.morphism = β.morphism) : α = β :=
begin
  induction α with α_morphism,
  induction β with β_morphism,
  tidy,
end

instance Arrows (C : Type (u₁+1)) [large_category C] : large_category (arrow C):=
{ hom  := arrow_hom,
  id   := by tidy,
  comp := λ X Y Z f g, ⟨ (f.morphism.1 ≫ g.morphism.1, f.morphism.2 ≫ g.morphism.2) ⟩ }

@[simp] lemma Arrows_comp {C : Type (u₁+1)} [large_category C] {X Y Z : arrow C} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = ⟨ (f.morphism.1 ≫ g.morphism.1, f.morphism.2 ≫ g.morphism.2) ⟩ := rfl

end category_theory.arrows

namespace category_theory.Functor

open category_theory.arrows

variable {C : Type (u₁+1)}
variable [large_category C]
variable {D : Type (u₂+1)}
variable [large_category D]

def onArrows : (C ↝ D) ↝ ((arrow C) ↝ (arrow D)) := 
{ obj := λ F,     { obj := λ X, ⟨ (F X.1.1, F X.1.2), F.map X.2 ⟩,
                    map := λ X Y f, ⟨ (F.map f.morphism.1, F.map f.morphism.2) ⟩ },
  map := λ F G τ, { app := λ X, ⟨ (τ X.1.1, τ X.1.2) ⟩ } }

end category_theory.Functor

