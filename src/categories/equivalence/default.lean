-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import categories.natural_isomorphism
import categories.functor.isomorphism

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.equivalence

universes u₁ u₂

structure Equivalence (C : Type (u₁+1)) [category C] (D : Type (u₂+1)) [category D] :=
  (functor : C ↝ D)
  (inverse : D ↝ C)
  (isomorphism_1 : (functor ⋙ inverse) ⇔ 1)
  (isomorphism_2 : (inverse ⋙ functor) ⇔ 1)

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

@[reducible] definition Equivalence.reverse (e : Equivalence C D) : Equivalence D C := {
  functor := e.inverse,
  inverse := e.functor,
  isomorphism_1 := e.isomorphism_2,
  isomorphism_2 := e.isomorphism_1
}

@[simp,ematch] lemma Equivalence.onMorphisms_1 (e : Equivalence C D) (X Y : D) (f : X ⟶ Y) : e.functor &> (e.inverse &> f) = (e.isomorphism_2.components X).morphism ≫ f ≫ (e.isomorphism_2.reverse.components Y).morphism := by obviously
@[simp,ematch] lemma Equivalence.onMorphisms_2 (e : Equivalence C D) (X Y : C) (f : X ⟶ Y) : e.inverse &> (e.functor &> f) = (e.isomorphism_1.components X).morphism ≫ f ≫ (e.isomorphism_1.reverse.components Y).morphism := by obviously

-- PROJECT a good way to do this?
-- definition EquivalenceComposition (e : Equivalence C D) (f : Equivalence D E) : Equivalence C E := 
-- {
--     functor := e.functor ⋙ f.functor,
--     inverse := f.inverse ⋙ e.inverse,
--     isomorphism_1 := sorry,
--     isomorphism_2 := sorry
-- }

class Full (F : C ↝ D) :=
  (preimage : ∀ {X Y : C} (f : (F +> X) ⟶ (F +> Y)), X ⟶ Y)
  (witness  : ∀ {X Y : C} (f : (F +> X) ⟶ (F +> Y)), F &> (preimage f) = f . obviously)

attribute [semiapplicable] Full.preimage
make_lemma Full.witness
attribute [simp,ematch] Full.witness_lemma

definition preimage (F : C ↝ D) [Full F] {X Y : C} (f : F +> X ⟶ F +> Y) : X ⟶ Y := Full.preimage f
@[simp] lemma image_preimage (F : C ↝ D) [Full F] {X Y : C} (f : F +> X ⟶ F +> Y) : F &> preimage F f = f := begin unfold preimage, obviously end

class Faithful (F : C ↝ D) :=
  (injectivity : ∀ {X Y : C} (f g : X ⟶ Y) (p : F &> f = F &> g), f = g)

make_lemma Faithful.injectivity
attribute [semiapplicable] Faithful.injectivity_lemma

definition preimage_iso (F : C ↝ D) [Full F] [Faithful F] {X Y : C} (f : (F +> X) ≅ (F +> Y)) : X ≅ Y := {
  morphism  := preimage F f.morphism,
  inverse   := preimage F f.inverse,
  witness_1 := begin apply @Faithful.injectivity _ _ _ _ F, tidy, end,
  witness_2 := begin apply @Faithful.injectivity _ _ _ _ F, tidy, end,
}

-- TODO
-- instance (F : C ↝ D) [Faithful F] : ReflectsIsomorphisms F := sorry

definition Embedding (F : C ↝ D) := (Full F) × (Faithful F)

definition EssentiallySurjective (F : C ↝ D) := Π d : D, Σ c : C, Isomorphism (F +> c) d
attribute [class] EssentiallySurjective

class is_Equivalence (F : Functor C D) := 
  (inverse       : Functor D C)
  (isomorphism_1 : (F ⋙ inverse) ⇔ 1)
  (isomorphism_2 : (inverse ⋙ F) ⇔ 1)

instance (e : Equivalence C D) : is_Equivalence e.functor := {
  inverse       := e.inverse,
  isomorphism_1 := e.isomorphism_1,
  isomorphism_2 := e.isomorphism_2,
}

end categories.equivalence