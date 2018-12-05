-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.equivalence

namespace category_theory

universes u u₁ v₁ u₂ v₂

structure idempotent (C : Type u₁) [category.{u₁ v₁} C] :=
(X : C)
(idem : X ⟶ X)
(w' : idem ≫ idem = idem . obviously)

restate_axiom idempotent.w'
attribute [simp,search] idempotent.w

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

namespace idempotent

structure morphism (P Q : idempotent.{u₁ v₁} C) :=
(hom : P.X ⟶ Q.X)
(left' : P.idem ≫ hom = hom . obviously)
(right' : hom ≫ Q.idem = hom . obviously)

restate_axiom morphism.left'
restate_axiom morphism.right'
attribute [simp,search] morphism.left morphism.right

@[extensionality] lemma ext {P Q : idempotent C} (f g : morphism P Q) (w : f.hom = g.hom) : f = g :=
begin
  induction f,
  induction g,
  tidy
end

end idempotent

instance idempotent_completion : category.{(max u₁ v₁) v₁} (idempotent C) :=
{ hom  := idempotent.morphism,
  id   := λ P, ⟨ P.idem ⟩,
  comp := λ _ _ _ f g, ⟨ f.hom ≫ g.hom ⟩ }

namespace idempotent_completion

@[simp] lemma id_hom (P : idempotent C) : ((𝟙 P) : idempotent.morphism P P).hom = P.idem := rfl
@[simp] lemma comp_hom {P Q R : idempotent C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

def to_completion (C : Type u₁) [𝒞 : category.{u₁ v₁} C] : C ⥤ (idempotent.{u₁ v₁} C) :=
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
{ functor := idempotent_functor,
  inverse := idempotent_inverse,
  fun_inv_id' :=
  { hom := { app := λ X, { hom := { hom := X.idem.hom } } },
    inv := { app := λ X, { hom := { hom := X.idem.hom } } } },
  inv_fun_id' :=
  { hom := { app := λ X, { hom := X.idem } },
    inv := { app := λ X, { hom := X.idem } } } }

variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
include 𝒟

def extend_to_completion (F : C ⥤ (idempotent D)) : (idempotent C) ⥤ (idempotent D) :=
{ obj := λ P,
  { X := (F.obj P.X).X,
    idem := (F.map P.idem).hom },
  map := λ _ _ f, { hom := (F.map f.hom).hom } }

end idempotent_completion
end category_theory
