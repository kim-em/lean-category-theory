-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.shape

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section equalizer
variables {Y Z : C}
structure is_equalizer {f g : Y ⟶ Z} (t : fork f g) :=
(lift : ∀ (s : fork f g), s.X ⟶ t.X)
(fac'  : ∀ (s : fork f g), (lift s) ≫ t.ι = s.ι . obviously)
(uniq' : ∀ (s : fork f g) (m : s.X ⟶ t.X) (w : m ≫ t.ι = s.ι), m = lift s . obviously)

restate_axiom is_equalizer.fac'
attribute [simp,search] is_equalizer.fac
restate_axiom is_equalizer.uniq'
attribute [search, back'] is_equalizer.uniq

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
  fac' := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))) }

end equalizer


section coequalizer
variables {Y Z : C}
structure is_coequalizer {f g : Z ⟶ Y} (t : cofork f g) :=
(desc : ∀ (s : cofork f g), t.X ⟶ s.X)
(fac'  : ∀ (s : cofork f g), t.π ≫ (desc s) = s.π . obviously)
(uniq' : ∀ (s : cofork f g) (m : t.X ⟶ s.X) (w : t.π ≫ m = s.π), m = desc s . obviously)

restate_axiom is_coequalizer.fac'
attribute [simp,search] is_coequalizer.fac
restate_axiom is_coequalizer.uniq'
attribute [search, back'] is_coequalizer.uniq

@[extensionality] lemma is_coequalizer.ext {f g : Z ⟶ Y} {t : cofork f g} (P Q : is_coequalizer t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_coequalizer.epi {f g : Z ⟶ Y} {t : cofork f g} (h : is_coequalizer t) : epi (t.π) :=
{ left_cancellation := λ X' k l w, begin 
                                    let s : cofork f g := { X := X', π := t.π ≫ k }, 
                                    have uniq_k := h.uniq s k (by obviously),
                                    have uniq_l := h.uniq s l (by obviously),
                                    obviously,
                              end }

lemma is_coequalizer.univ {f g : Z ⟶ Y} {t : cofork f g} (h : is_coequalizer t) (s : cofork f g) (φ : t.X ⟶ s.X) : (t.π ≫ φ = s.π) ↔ (φ = h.desc s) :=
begin
obviously
end

def is_coequalizer.of_desc_univ {f g : Z ⟶ Y} {t : cofork f g}
  (desc : Π (s : cofork f g), t.X ⟶ s.X)
  (univ : Π (s : cofork f g) (φ : t.X ⟶ s.X), (t.π ≫ φ = s.π) ↔ (φ = desc s)) : is_coequalizer t :=
{ desc := desc,
  fac' := λ s, ((univ s (desc s)).mpr (eq.refl (desc s))) }

end coequalizer

variable (C)

class has_equalizers :=
(equalizer : Π {Y Z : C} (f g : Y ⟶ Z), fork f g)
(is_equalizer : Π {Y Z : C} (f g : Y ⟶ Z), is_equalizer (equalizer f g) . obviously)

class has_coequalizers :=
(coequalizer : Π {Y Z : C} (f g : Y ⟶ Z), cofork f g)
(is_coequalizer : Π {Y Z : C} (f g : Y ⟶ Z), is_coequalizer (coequalizer f g) . obviously)

variable {C}



section
variables [has_equalizers.{u v} C] {Y Z : C} (f g : Y ⟶ Z)

def equalizer.fork := has_equalizers.equalizer.{u v} f g
def equalizer := (equalizer.fork f g).X
def equalizer.ι : (equalizer f g) ⟶ Y := (equalizer.fork f g).ι
@[search] def equalizer.w : (equalizer.ι f g) ≫ f = (equalizer.ι f g) ≫ g := (equalizer.fork f g).w
def equalizer.universal_property : is_equalizer (equalizer.fork f g) := has_equalizers.is_equalizer.{u v} C f g

variables {f g}

def equalizer.lift {P : C} (h : P ⟶ Y) (w : h ≫ f = h ≫ g) : P ⟶ equalizer f g := 
(equalizer.universal_property f g).lift { X := P, ι := h, w' := w }

lemma equalizer.lift_ι {P : C} (h : P ⟶ Y) (w : h ≫ f = h ≫ g) : equalizer.lift h w ≫ equalizer.ι f g = h := by obviously

@[extensionality] lemma equalizer.hom_ext {X : C} (h k : X ⟶ equalizer f g) (w : h ≫ equalizer.ι f g = k ≫ equalizer.ι f g) : h = k :=
begin
  let s : fork f g := ⟨ ⟨ X ⟩, h ≫ equalizer.ι f g ⟩,
  have q := (equalizer.universal_property f g).uniq s h,
  have p := (equalizer.universal_property f g).uniq s k,
  rw [q, ←p],
  solve_by_elim, refl
end

-- There are many lemmas one could prove here, analogous to those in products.lean and limits.lean.
-- (e.g. how equalizers transform under functors, that equalizer f g ≅ equalizer g f, ...)
-- They can wait until needed.

end

section
variables [has_coequalizers.{u v} C] {Y Z : C} (f g : Y ⟶ Z)

def coequalizer.cofork := has_coequalizers.coequalizer.{u v} f g
def coequalizer := (coequalizer.cofork f g).X
def coequalizer.π : Z ⟶ (coequalizer f g) := (coequalizer.cofork f g).π
@[search] def coequalizer.w : f ≫ (coequalizer.π f g)  = g ≫ (coequalizer.π f g) := (coequalizer.cofork f g).w
def coequalizer.universal_property : is_coequalizer (coequalizer.cofork f g) := has_coequalizers.is_coequalizer.{u v} C f g

variables {f g}

def coequalizer.desc {P : C} (h : Z ⟶ P) (w : f ≫ h = g ≫ h) : coequalizer f g ⟶ P := 
(coequalizer.universal_property f g).desc { X := P, π := h, w' := w }

lemma coequalizer.desc_π {P : C} (h : Z ⟶ P) (w : f ≫ h = g ≫ h) : coequalizer.π f g ≫ coequalizer.desc h w = h := by obviously

@[extensionality] lemma coequalizer.hom_ext {X : C} (h k : coequalizer f g ⟶ X) (w : coequalizer.π f g ≫ h = coequalizer.π f g ≫ k) : h = k :=
begin
  let s : cofork f g := ⟨ ⟨ X ⟩, coequalizer.π f g ≫ h ⟩,
  have q := (coequalizer.universal_property f g).uniq s h,
  have p := (coequalizer.universal_property f g).uniq s k,
  rw [q, ←p],
  solve_by_elim, refl
end

end

end category_theory.limits
