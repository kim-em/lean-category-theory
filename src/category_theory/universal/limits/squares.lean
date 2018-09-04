-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.universal.limits.shape
import category_theory.filtered

open category_theory


namespace category_theory.universal

universes u v w

section

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section pullback
variables {Y₁ Y₂ Z : C} {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} 
structure is_pullback (t : square r₁ r₂) :=
(lift : ∀ (s : square r₁ r₂), s.X ⟶ t.X)
(fac₁ : ∀ (s : square r₁ r₂), (lift s ≫ t.π₁) = s.π₁ . obviously)
(fac₂ : ∀ (s : square r₁ r₂), (lift s ≫ t.π₂) = s.π₂ . obviously)
(uniq : ∀ (s : square r₁ r₂) (m : s.X ⟶ t.X) (w₁ : (m ≫ t.π₁) = s.π₁) (w₂ : (m ≫ t.π₂) = s.π₂), m = lift s . obviously)

restate_axiom is_pullback.fac₁
attribute [simp,search] is_pullback.fac₁_lemma
restate_axiom is_pullback.fac₂
attribute [simp,search] is_pullback.fac₂_lemma
restate_axiom is_pullback.uniq
attribute [search, back'] is_pullback.uniq_lemma

@[extensionality] lemma is_pullback.ext {t : square r₁ r₂} (P Q : is_pullback t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_pullback.univ {t : square r₁ r₂} (h : is_pullback t) (s : square r₁ r₂) (φ : s.X ⟶ t.X) : 
  (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_pullback.of_lift_univ {t : square r₁ r₂}
  (lift : Π (s : square r₁ r₂), s.X ⟶ t.X)
  (univ : Π (s : square r₁ r₂) (φ : s.X ⟶ t.X), (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = lift s)) : 
  is_pullback t :=
{ lift := lift,
  fac₁ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).left,
  fac₂ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).right,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

end pullback

variable (C)

class has_pullbacks :=
(pullback : Π {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z), square r₁ r₂)
(is_pullback : Π {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z), is_pullback (pullback r₁ r₂) . obviously)

variable {C}


section
variables [has_pullbacks.{u v} C] {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z)

def pullback.square := has_pullbacks.pullback.{u v} r₁ r₂
def pullback := (pullback.square r₁ r₂).X
def pullback.π₁ : pullback r₁ r₂ ⟶ Y₁ := (pullback.square r₁ r₂).π₁
def pullback.π₂ : pullback r₁ r₂ ⟶ Y₂ := (pullback.square r₁ r₂).π₂
def pullback.universal_property : is_pullback (pullback.square r₁ r₂) := has_pullbacks.is_pullback.{u v} C r₁ r₂

@[extensionality] lemma pullback.hom_ext 
  {X : C} (f g : X ⟶ pullback r₁ r₂) 
  (w₁ : f ≫ pullback.π₁ r₁ r₂ = g ≫ pullback.π₁ r₁ r₂) 
  (w₂ : f ≫ pullback.π₂ r₁ r₂ = g ≫ pullback.π₂ r₁ r₂) : f = g :=
begin
  let s : square r₁ r₂ := ⟨ ⟨ X ⟩, f ≫ pullback.π₁ r₁ r₂, f ≫ pullback.π₂ r₁ r₂ ⟩,
  have q := (pullback.universal_property r₁ r₂).uniq s f,
  have p := (pullback.universal_property r₁ r₂).uniq s g,
  rw [q, ←p],
  obviously,
end


end
