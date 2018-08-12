-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..embedding

namespace category_theory

universes u₁ v₁ u₂ v₂

structure Equivalence (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] :=
  (functor : C ↝ D)
  (inverse : D ↝ C)
  (isomorphism_1 : (functor ⋙ inverse) ⇔ (category_theory.functor.id C) . obviously')
  (isomorphism_2 : (inverse ⋙ functor) ⇔ (category_theory.functor.id D) . obviously')

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

namespace Equivalence

def symm (e : Equivalence C D) : Equivalence D C := 
{ functor := e.inverse,
  inverse := e.functor,
  isomorphism_1 := e.isomorphism_2,
  isomorphism_2 := e.isomorphism_1 }

@[simp,ematch] lemma onMorphisms_1 (e : Equivalence C D) (X Y : D) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = (e.isomorphism_2.hom X) ≫ f ≫ (e.isomorphism_2.inv Y) := by obviously'
@[simp,ematch] lemma onMorphisms_2 (e : Equivalence C D) (X Y : C) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = (e.isomorphism_1.hom X) ≫ f ≫ (e.isomorphism_1.inv Y) := by obviously'

-- PROJECT a good way to do this?
-- def EquivalenceComposition (e : Equivalence C D) (f : Equivalence D E) : Equivalence C E := 
-- {
--     functor := e.functor ⋙ f.functor,
--     inverse := f.inverse ⋙ e.inverse,
--     isomorphism_1 := sorry,
--     isomorphism_2 := sorry
-- }
end Equivalence


def EssentiallySurjective (F : C ↝ D) := Π d : D, Σ c : C, (F c) ≅ d
attribute [class] EssentiallySurjective

class is_Equivalence (F : C ↝ D) := 
(inverse       : D ↝ C)
(isomorphism_1 : (F ⋙ inverse) ⇔ (functor.id C))
(isomorphism_2 : (inverse ⋙ F) ⇔ (functor.id D))

instance (e : Equivalence C D) : is_Equivalence e.functor := 
{ inverse       := e.inverse,
  isomorphism_1 := e.isomorphism_1,
  isomorphism_2 := e.isomorphism_2 }

end category_theory