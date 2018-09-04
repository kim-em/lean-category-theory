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

section equalizer
variables {Y Z : C}
structure is_equalizer {f g : Y ⟶ Z} (t : fork f g) :=
(lift : ∀ (s : fork f g), s.X ⟶ t.X)
(fac  : ∀ (s : fork f g), (lift s) ≫ t.ι = s.ι . obviously)
(uniq : ∀ (s : fork f g) (m : s.X ⟶ t.X) (w : m ≫ t.ι = s.ι), m = lift s . obviously)

restate_axiom is_equalizer.fac
attribute [simp,search] is_equalizer.fac_lemma
restate_axiom is_equalizer.uniq
attribute [search, back'] is_equalizer.uniq_lemma

@[extensionality] lemma is_equalizer.ext {f g : Y ⟶ Z} {t : fork f g} (P Q : is_equalizer t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_equalizer.mono {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) : mono (t.ι) :=
{ right_cancellation := λ X' k l w, begin 
                                    let s : fork f g := { X := X', ι := k ≫ t.ι }, 
                                    have uniq_k := h.uniq s k (by obviously),
                                    have uniq_l := h.uniq s l (by obviously),
                                    obviously,
                              end }

lemma is_equalizer.univ {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) (s : fork f g) (φ : s.X ⟶ t.X) : (φ ≫ t.ι = s.ι) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_equalizer.of_lift_univ {f g : Y ⟶ Z} {t : fork f g}
  (lift : Π (s : fork f g), s.X ⟶ t.X)
  (univ : Π (s : fork f g) (φ : s.X ⟶ t.X), (φ ≫ t.ι = s.ι) ↔ (φ = lift s)) : is_equalizer t :=
{ lift := lift,
  fac := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))),
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

end equalizer


variable (C)

class has_equalizers :=
(equalizer : Π {Y Z : C} (f g : Y ⟶ Z), fork f g)
(is_equalizer : Π {Y Z : C} (f g : Y ⟶ Z), is_equalizer (equalizer f g) . obviously)

variable {C}



section
variables [has_equalizers.{u v} C] {Y Z : C} (f g : Y ⟶ Z)

def equalizer.fork := has_equalizers.equalizer.{u v} f g
def equalizer := (equalizer.fork f g).X
def equalizer.ι : (equalizer f g) ⟶ Y := (equalizer.fork f g).ι
@[search] def equalizer.w : (equalizer.ι f g) ≫ f = (equalizer.ι f g) ≫ g := (equalizer.fork f g).w
def equalizer.universal_property : is_equalizer (equalizer.fork f g) := has_equalizers.is_equalizer.{u v} C f g

def equalizer.lift (P : C) (h : P ⟶ Y) (w : h ≫ f = h ≫ g) : P ⟶ equalizer f g := 
(equalizer.universal_property f g).lift { X := P, ι := h, w := w }

@[extensionality] lemma equalizer.hom_ext {Y Z : C} {f g : Y ⟶ Z} {X : C} (h k : X ⟶ equalizer f g) (w : h ≫ equalizer.ι f g = k ≫ equalizer.ι f g) : h = k :=
begin
  let s : fork f g := ⟨ ⟨ X ⟩, h ≫ equalizer.ι f g ⟩,
  have q := (equalizer.universal_property f g).uniq s h,
  have p := (equalizer.universal_property f g).uniq s k,
  rw [q, ←p],
  solve_by_elim, refl
end

end