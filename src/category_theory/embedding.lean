-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.isomorphism
import category_theory.tactics.obviously

namespace category_theory

universes u₁ v₁ u₂ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

class full (F : C ⥤ D) :=
(preimage : ∀ {X Y : C} (f : (F X) ⟶ (F Y)), X ⟶ Y)
(witness'  : ∀ {X Y : C} (f : (F X) ⟶ (F Y)), F.map (preimage f) = f . obviously)

attribute [back'] full.preimage
restate_axiom full.witness'
attribute [simp,search] full.witness

instance : full (functor.id C) :=
{ preimage := λ _ _ f, f }

def preimage (F : C ⥤ D) [full F] {X Y : C} (f : F X ⟶ F Y) : X ⟶ Y := full.preimage.{u₁ v₁ u₂ v₂}  f
@[simp,search] lemma image_preimage (F : C ⥤ D) [full F] {X Y : C} (f : F X ⟶ F Y) : F.map (preimage F f) = f := begin unfold preimage, obviously end

class faithful (F : C ⥤ D) : Prop :=
(injectivity' : ∀ {X Y : C} {f g : X ⟶ Y} (p : F.map f = F.map g), f = g)

restate_axiom faithful.injectivity'
attribute [forward] faithful.injectivity

instance : faithful (functor.id C) := by obviously

section
variables  {F : C ⥤ D} [full F] [faithful F] {X Y : C}
def preimage_iso (f : (F X) ≅ (F Y)) : X ≅ Y := 
{ hom := preimage F (f : F X ⟶ F Y),
  inv := preimage F (f.symm : F Y ⟶ F X),
  hom_inv_id' := begin apply @faithful.injectivity _ _ _ _ F, obviously, end,
  inv_hom_id' := begin apply @faithful.injectivity _ _ _ _ F, obviously, end, }

@[simp] lemma preimage_iso_coe (f : (F X) ≅ (F Y)) : ((preimage_iso f) : X ⟶ Y) = preimage F (f : F X ⟶ F Y) := rfl
@[simp] lemma preimage_iso_symm_coe (f : (F X) ≅ (F Y)) : ((preimage_iso f).symm : Y ⟶ X) = preimage F (f.symm : F Y ⟶ F X) := rfl
end

class embedding (F : C ⥤ D) extends (full F), (faithful F).

-- TODO remove?
@[back] def embedding.ext (F : C ⥤ D) (full : full F) (faithful : faithful F) : embedding F := by obviously

end category_theory