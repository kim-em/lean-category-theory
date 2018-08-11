-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import categories.natural_isomorphism
import categories.functor.isomorphism

namespace category_theory

universes u₁ v₁ u₂ v₂

structure Equivalence (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] :=
  (functor : C ↝ D)
  (inverse : D ↝ C)
  (isomorphism_1 : (functor ⋙ inverse) ⇔ (category_theory.functor.id C) . obviously')
  (isomorphism_2 : (inverse ⋙ functor) ⇔ (category_theory.functor.id D) . obviously')

namespace Equivalence

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

definition symm (e : Equivalence C D) : Equivalence D C := 
{ functor := e.inverse,
  inverse := e.functor,
  isomorphism_1 := e.isomorphism_2,
  isomorphism_2 := e.isomorphism_1 }

@[simp,ematch] lemma onMorphisms_1 (e : Equivalence C D) (X Y : D) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = (e.isomorphism_2.hom X) ≫ f ≫ (e.isomorphism_2.inv Y) := by obviously'
@[simp,ematch] lemma onMorphisms_2 (e : Equivalence C D) (X Y : C) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = (e.isomorphism_1.hom X) ≫ f ≫ (e.isomorphism_1.inv Y) := by obviously'

-- PROJECT a good way to do this?
-- definition EquivalenceComposition (e : Equivalence C D) (f : Equivalence D E) : Equivalence C E := 
-- {
--     functor := e.functor ⋙ f.functor,
--     inverse := f.inverse ⋙ e.inverse,
--     isomorphism_1 := sorry,
--     isomorphism_2 := sorry
-- }
end Equivalence

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

class Full (F : C ↝ D) :=
(preimage : ∀ {X Y : C} (f : (F X) ⟶ (F Y)), X ⟶ Y)
(witness  : ∀ {X Y : C} (f : (F X) ⟶ (F Y)), F.map (preimage f) = f . obviously)

attribute [backwards_cautiously] Full.preimage
restate_axiom Full.witness
attribute [simp,ematch] Full.witness_lemma
set_option pp.universes true
definition preimage (F : C ↝ D) [Full F] {X Y : C} (f : F X ⟶ F Y) : X ⟶ Y := Full.preimage.{u₁ v₁ u₂ v₂}  f
@[simp] lemma image_preimage (F : C ↝ D) [Full F] {X Y : C} (f : F X ⟶ F Y) : F.map (preimage F f) = f := begin unfold preimage, obviously' end

class Faithful (F : C ↝ D) :=
  (injectivity : ∀ {X Y : C} {f g : X ⟶ Y} (p : F.map f = F.map g), f = g)

restate_axiom Faithful.injectivity
attribute [forwards] Faithful.injectivity_lemma

definition preimage_iso {F : C ↝ D} [Full F] [Faithful F] {X Y : C} (f : (F X) ≅ (F Y)) : X ≅ Y := 
{ hom := preimage F f.hom,
  inv := preimage F f.inv,
  hom_inv_id := begin apply @Faithful.injectivity _ _ _ _ F, tidy, end,
  inv_hom_id := begin apply @Faithful.injectivity _ _ _ _ F, tidy, end, }

-- TODO
-- instance (F : C ↝ D) [Faithful F] : ReflectsIsomorphisms F := sorry

definition Embedding (F : C ↝ D) := (Full F) × (Faithful F)

definition EssentiallySurjective (F : C ↝ D) := Π d : D, Σ c : C, (F c) ≅ d
attribute [class] EssentiallySurjective
end

section

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

class is_Equivalence (F : C ↝ D) := 
(inverse       : D ↝ C)
(isomorphism_1 : (F ⋙ inverse) ⇔ (functor.id C))
(isomorphism_2 : (inverse ⋙ F) ⇔ (functor.id D))

instance (e : Equivalence C D) : is_Equivalence e.functor := 
{ inverse       := e.inverse,
  isomorphism_1 := e.isomorphism_1,
  isomorphism_2 := e.isomorphism_2 }
end

end category_theory