-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.natural_isomorphism

namespace category_theory

universes u₁ v₁ u₂ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

class full (F : C ↝ D) :=
(preimage : ∀ {X Y : C} (f : (F X) ⟶ (F Y)), X ⟶ Y)
(witness  : ∀ {X Y : C} (f : (F X) ⟶ (F Y)), F.map (preimage f) = f . obviously)

attribute [back'] full.preimage
restate_axiom full.witness
attribute [simp,ematch] full.witness_lemma
set_option pp.universes true
def preimage (F : C ↝ D) [full F] {X Y : C} (f : F X ⟶ F Y) : X ⟶ Y := full.preimage.{u₁ v₁ u₂ v₂}  f
@[simp] lemma image_preimage (F : C ↝ D) [full F] {X Y : C} (f : F X ⟶ F Y) : F.map (preimage F f) = f := begin unfold preimage, obviously end

class faithful (F : C ↝ D) :=
  (injectivity : ∀ {X Y : C} {f g : X ⟶ Y} (p : F.map f = F.map g), f = g)

restate_axiom faithful.injectivity
attribute [forward] faithful.injectivity_lemma

def preimage_iso {F : C ↝ D} [full F] [faithful F] {X Y : C} (f : (F X) ≅ (F Y)) : X ≅ Y := 
{ hom := preimage F f.hom,
  inv := preimage F f.inv,
  hom_inv_id' := begin apply @faithful.injectivity _ _ _ _ F, tidy, end,
  inv_hom_id' := begin apply @faithful.injectivity _ _ _ _ F, tidy, end, }

-- TODO
-- instance (F : C ↝ D) [Faithful F] : ReflectsIsomorphisms F := sorry

class embedding (F : C ↝ D) extends (full F), (faithful F).

@[back] def embedding.ext (F : C ↝ D) (full : full F) (faithful : faithful F) : embedding F := by obviously

end category_theory