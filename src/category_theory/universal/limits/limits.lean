-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.universal.limits.shape
import category_theory.filtered

open category_theory


namespace category_theory.universal

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section limit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

structure is_limit {F : J ↝ C} (t : cone F) :=
(lift : ∀ (s : cone F), s.X ⟶ t.X)
(fac  : ∀ (s : cone F) (j : J), (lift s ≫ t.π j) = s.π j . obviously)
(uniq : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, (m ≫ t.π j) = s.π j), m = lift s . obviously)

restate_axiom is_limit.fac
attribute [simp,ematch] is_limit.fac_lemma
restate_axiom is_limit.uniq
attribute [ematch, back'] is_limit.uniq_lemma

@[extensionality] lemma is_limit.ext {F : J ↝ C} {t : cone F} (P Q : is_limit t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_limit.univ {F : J ↝ C} {t : cone F} (h : is_limit t) (s : cone F) (φ : s.X ⟶ t.X) : (∀ j, φ ≫ t.π j = s.π j) ↔ (φ = h.lift s) :=
begin
obviously,
end

def is_limit.of_lift_univ {F : J ↝ C} {t : cone F}
  (lift : Π (s : cone F), s.X ⟶ t.X)
  (univ : Π (s : cone F) (φ : s.X ⟶ t.X), (∀ j : J, (φ ≫ t.π j) = s.π j) ↔ (φ = lift s)) : is_limit t :=
{ lift := lift,
  fac  := λ s j, ((univ s (lift s)).mpr (eq.refl (lift s))) j,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

lemma homs_to_limit_ext  {F : J ↝ C} (c : cone.{u v} F) (B : is_limit c) {X : C} (f g : X ⟶ c.X) (w : ∀ j, f ≫ c.π j = g ≫ c.π j) : f = g :=
begin
  let s : cone F := ⟨ ⟨ X ⟩, λ j, f ≫ c.π j, by obviously ⟩,
  have q := B.uniq s f,
  have p := B.uniq s g,
  rw [q, ←p],
  intros,
  rw ← w j,
  intros,
  refl
end

end limit


section colimit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

structure is_colimit {F : J ↝ C} (t : cocone F) :=
(desc : ∀ (s : cocone F), t.X ⟶ s.X)
(fac  : ∀ (s : cocone F) (j : J), (t.ι j ≫ desc s) = s.ι j . obviously)
(uniq : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, (t.ι j ≫ m) = s.ι j), m = desc s . obviously)

restate_axiom is_colimit.fac
attribute [simp,ematch] is_colimit.fac_lemma
restate_axiom is_colimit.uniq
attribute [ematch, back'] is_colimit.uniq_lemma

@[extensionality] lemma is_colimit.ext {F : J ↝ C} {t : cocone F} (P Q : is_colimit t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_colimit.univ {F : J ↝ C} {t : cocone F} (h : is_colimit t) (s : cocone F) (φ : t.X ⟶ s.X) : (∀ j, t.ι j ≫ φ = s.ι j) ↔ (φ = h.desc s) :=
begin
obviously,
end

def is_colimit.of_desc_univ {F : J ↝ C} {t : cocone F}
  (desc : Π (s : cocone F), t.X ⟶ s.X)
  (univ : Π (s : cocone F) (φ : t.X ⟶ s.X), (∀ j : J, (t.ι j ≫ φ) = s.ι j) ↔ (φ = desc s)) : is_colimit t :=
{ desc := desc,
  fac  := λ s j, ((univ s (desc s)).mpr (eq.refl (desc s))) j,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

end colimit

variable (C)

class has_limits :=
(limit : Π {J : Type v} [𝒥 : small_category J] (F : J ↝ C), cone F)
(is_limit : Π {J : Type v} [𝒥 : small_category J] (F : J ↝ C), is_limit (limit F) . obviously)

class has_filtered_limits :=
(limit : Π {J : Type v} [𝒥 : small_category J] [filtered.{v v} J] (F : J ↝ C), cone F)
(is_limit : Π {J : Type v} [𝒥 : small_category J] [filtered.{v v} J] (F : J ↝ C), is_limit (limit F) . obviously)

-- also do finite limits?

variable {C}

section
variables [has_limits.{u v} C] {J : Type v} [𝒥 : small_category J] 
include 𝒥

def limit.cone (F : J ↝ C) : cone F := has_limits.limit.{u v} F
def limit (F : J ↝ C) := (limit.cone F).X
def limit.π (F : J ↝ C) (j : J) : limit F ⟶ F j := (limit.cone F).π j
def limit.universal_property (F : J ↝ C) : is_limit (limit.cone F) := 
has_limits.is_limit.{u v} C F
-- limit.cone is in cones.lean

-- FIXME why the @?
@[simp] lemma limit.cone_π (F : J ↝ C) (j : J) : (limit.cone F).π j = (@limit.π C _ _ J _ F j) := rfl

@[back] def limit.hom_characterisation (F : J ↝ C) (c : cone F)
  (f g : c.X ⟶ limit F)
  (w_f : ∀ j, f ≫ limit.π F j = c.π j)
  (w_g : ∀ j, g ≫ limit.π F j = c.π j) : f = g :=
begin
  have p_f := (limit.universal_property.{u v} F).uniq c f (by obviously),
  have p_g := (limit.universal_property.{u v} F).uniq c g (by obviously),
  obviously,
end
end

variable (C)

class has_colimits :=
(colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ↝ C), cocone F)
(is_colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ↝ C), is_colimit (colimit F) . obviously)

class has_filtered_colimits :=
(colimit : Π {J : Type v} [𝒥 : small_category J] [filtered.{v v} J] (F : J ↝ C), cocone F)
(is_colimit : Π {J : Type v} [𝒥 : small_category J] [filtered.{v v} J] (F : J ↝ C), is_colimit (colimit F) . obviously)

variable {C}

section
variables [has_colimits.{u v} C] {J : Type v} [𝒥 : small_category J] 
include 𝒥

def colimit.cocone (F : J ↝ C) : cocone F := has_colimits.colimit.{u v} F
def colimit (F : J ↝ C) := (colimit.cocone F).X
def colimit.ι (F : J ↝ C) (j : J) : F j ⟶ colimit F := (colimit.cocone F).ι j
def colimit.universal_property (F : J ↝ C) : is_colimit (colimit.cocone F) := 
has_colimits.is_colimit.{u v} C F

@[back] def colimit.hom_characterisation (F : J ↝ C) (c : cocone F)
  (f g : colimit F ⟶ c.X)
  (w_f : ∀ j, colimit.ι F j ≫ f = c.ι j)
  (w_g : ∀ j, colimit.ι F j ≫ g = c.ι j) : f = g :=
begin
  have p_f := (colimit.universal_property.{u v} F).uniq c f (by obviously),
  have p_g := (colimit.universal_property.{u v} F).uniq c g (by obviously),
  obviously,
end

end
end category_theory.universal