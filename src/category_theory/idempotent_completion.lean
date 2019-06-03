-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import category_theory.tactics.obviously
import category_theory.equivalence

namespace category_theory

universes v₁ v₂ u₁ u₂

structure idempotent (C : Sort u₁) [category.{v₁+1} C] :=
(X : C)
(idem : X ⟶ X)
(w' : idem ≫ idem = idem . obviously)

restate_axiom idempotent.w'
attribute [simp] idempotent.w -- search

variables {C : Sort u₁} [𝒞 : category.{v₁+1} C]
include 𝒞

namespace idempotent

structure morphism (P Q : idempotent.{v₁} C) :=
(hom : P.X ⟶ Q.X)
(left' : P.idem ≫ hom = hom . obviously)
(right' : hom ≫ Q.idem = hom . obviously)

restate_axiom morphism.left'
restate_axiom morphism.right'
attribute [simp] morphism.left morphism.right -- search

@[extensionality] lemma ext {P Q : idempotent C} (f g : morphism P Q) (w : f.hom = g.hom) : f = g :=
begin
  induction f,
  induction g,
  tidy
end

end idempotent

instance idempotent_completion : category.{v₁+1} (idempotent C) :=
{ hom  := idempotent.morphism,
  id   := λ P, ⟨ P.idem ⟩,
  comp := λ _ _ _ f g,
  { hom := f.hom ≫ g.hom,
    left'  := by rw [←category.assoc, idempotent.morphism.left],
    right' := by rw [category.assoc, idempotent.morphism.right] } }

namespace idempotent_completion

@[simp] lemma id_hom (P : idempotent C) : ((𝟙 P) : idempotent.morphism P P).hom = P.idem := rfl
@[simp] lemma comp_hom {P Q R : idempotent C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

def to_completion (C : Type u₁) [𝒞 : category.{v₁+1} C] : C ⥤ (idempotent.{v₁} C) :=
{ obj := λ P, { X := P, idem := 𝟙 P },
  map := λ _ _ f, { hom := f } }

@[simp] private lemma double_idempotent_morphism_left (P Q : idempotent (idempotent C)) (f : P ⟶ Q)
  : (P.idem).hom ≫ (f.hom).hom = (f.hom).hom := congr_arg idempotent.morphism.hom f.left
@[simp] private lemma double_idempotent_morphism_right (P Q : idempotent (idempotent C)) (f : P ⟶ Q)
  : (f.hom).hom ≫ (Q.idem).hom = (f.hom).hom := congr_arg idempotent.morphism.hom f.right

@[simp] private def idempotent_functor : (idempotent (idempotent C)) ⥤ (idempotent C) :=
{ obj := λ P, ⟨ P.X.X, P.idem.hom, congr_arg idempotent.morphism.hom P.w ⟩,
  map := λ _ _ f, ⟨ f.hom.hom, by obviously ⟩ }.
@[simp] private def idempotent_inverse : (idempotent C) ⥤ (idempotent (idempotent C)) :=
{ obj := λ P, ⟨ P, ⟨ P.idem, by obviously ⟩, by obviously ⟩,
  map := λ _ _ f, ⟨ f, by obviously ⟩ }.

@[simp] lemma idem_hom_idempotent (X : idempotent (idempotent C)) : X.idem.hom ≫ X.idem.hom = X.idem.hom :=
begin
  rw ←comp_hom,
  simp,
end

lemma idempotent_idempotent :
  equivalence (idempotent (idempotent C)) (idempotent C) :=
equivalence.mk idempotent_functor idempotent_inverse
  { hom := { app := λ X, { hom := { hom := X.idem.hom } } },
    inv := { app := λ X, { hom := { hom := X.idem.hom } } } }
  { hom := { app := λ X, { hom := X.idem } },
    inv := { app := λ X, { hom := X.idem } } }

variable {D : Type u₂}
variable [𝒟 : category.{v₂+1} D]
include 𝒟

attribute [search] idempotent.w idempotent.morphism.left idempotent.morphism.right
  idem_hom_idempotent comp_hom id_hom

def extend_to_completion (F : C ⥤ (idempotent D)) : (idempotent C) ⥤ (idempotent D) :=
{ obj := λ P,
  { X := (F.obj P.X).X,
    idem := (F.map P.idem).hom,
    w' := begin rw [←comp_hom, ←functor.map_comp, idempotent.w], end },
  map := λ X Y f, { hom := (F.map f.hom).hom } }

end idempotent_completion
end category_theory
