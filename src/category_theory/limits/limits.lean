-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.shape
import category_theory.filtered

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section limit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

structure is_limit {F : J ⥤ C} (t : cone F) :=
(lift : ∀ (s : cone F), s.X ⟶ t.X)
(fac  : ∀ (s : cone F) (j : J), (lift s ≫ t.π j) = s.π j . obviously)
(uniq : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, (m ≫ t.π j) = s.π j), m = lift s . obviously)

restate_axiom is_limit.fac
attribute [simp,search] is_limit.fac_lemma
restate_axiom is_limit.uniq
attribute [search,back'] is_limit.uniq_lemma

@[extensionality] lemma is_limit.ext {F : J ⥤ C} {t : cone F} (P Q : is_limit t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_limit.univ {F : J ⥤ C} {t : cone F} (h : is_limit t) (s : cone F) (φ : s.X ⟶ t.X) : (∀ j, φ ≫ t.π j = s.π j) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_limit.of_lift_univ {F : J ⥤ C} {t : cone F}
  (lift : Π (s : cone F), s.X ⟶ t.X)
  (univ : Π (s : cone F) (φ : s.X ⟶ t.X), (∀ j : J, (φ ≫ t.π j) = s.π j) ↔ (φ = lift s)) : is_limit t :=
{ lift := lift,
  fac  := λ s j, ((univ s (lift s)).mpr (eq.refl (lift s))) j,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

end limit


section colimit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

structure is_colimit {F : J ⥤ C} (t : cocone F) :=
(desc : ∀ (s : cocone F), t.X ⟶ s.X)
(fac  : ∀ (s : cocone F) (j : J), (t.ι j ≫ desc s) = s.ι j . obviously)
(uniq : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, (t.ι j ≫ m) = s.ι j), m = desc s . obviously)

restate_axiom is_colimit.fac
attribute [simp,search] is_colimit.fac_lemma
restate_axiom is_colimit.uniq
attribute [search,back'] is_colimit.uniq_lemma

@[extensionality] lemma is_colimit.ext {F : J ⥤ C} {t : cocone F} (P Q : is_colimit t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_colimit.univ {F : J ⥤ C} {t : cocone F} (h : is_colimit t) (s : cocone F) (φ : t.X ⟶ s.X) : (∀ j, t.ι j ≫ φ = s.ι j) ↔ (φ = h.desc s) :=
begin
obviously,
end

def is_colimit.of_desc_univ {F : J ⥤ C} {t : cocone F}
  (desc : Π (s : cocone F), t.X ⟶ s.X)
  (univ : Π (s : cocone F) (φ : t.X ⟶ s.X), (∀ j : J, (t.ι j ≫ φ) = s.ι j) ↔ (φ = desc s)) : is_colimit t :=
{ desc := desc,
  fac  := λ s j, ((univ s (desc s)).mpr (eq.refl (desc s))) j,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

end colimit

variable (C)

class has_limits :=
(limit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), cone F)
(is_limit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), is_limit (limit F) . obviously)

class has_filtered_limits :=
(limit : Π {J : Type v} [𝒥 : small_category J] [filtered.{v v} J] (F : J ⥤ C), cone F)
(is_limit : Π {J : Type v} [𝒥 : small_category J] [filtered.{v v} J] (F : J ⥤ C), is_limit (limit F) . obviously)

-- also do finite limits?

variable {C}

section
variables [has_limits.{u v} C] {J : Type v} [𝒥 : small_category J] 
include 𝒥

def limit.cone (F : J ⥤ C) : cone F := has_limits.limit.{u v} F
def limit (F : J ⥤ C) := (limit.cone F).X
def limit.π (F : J ⥤ C) (j : J) : limit F ⟶ F j := (limit.cone F).π j
def limit.universal_property (F : J ⥤ C) : is_limit (limit.cone F) := 
has_limits.is_limit.{u v} C F

def limit.lift (F : J ⥤ C) (c : cone F) : c.X ⟶ limit F := (limit.universal_property F).lift c

@[simp] def limit.universal_property_lift (F : J ⥤ C) (c : cone F) : (limit.universal_property F).lift c = limit.lift F c := rfl
@[simp] def limit.lift_π (F : J ⥤ C) (c : cone F) (j : J) : (limit.universal_property F).lift c ≫ limit.π F j = c.π j :=
(limit.universal_property F).fac c j


-- FIXME why the @?
@[simp] lemma limit.cone_π (F : J ⥤ C) (j : J) : (limit.cone F).π j = (@limit.π C _ _ J _ F j) := rfl

-- TODO needs a home
def cone.pullback {F : J ⥤ C} (A : cone F) {X : C} (f : X ⟶ A.X) : cone F :=
{ X := X,
  π := λ j, f ≫ A.π j }

-- lemma limit.pullback_lift (F : J ⥤ C) (c : cone F) {X : C} (f : X ⟶ c.X) : f ≫ limit.lift F c = limit.lift F (c.pullback f) := sorry

@[extensionality] def limit.hom_ext {F : J ⥤ C} {c : cone F}
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
(colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), cocone F)
(is_colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), is_colimit (colimit F) . obviously)

class has_filtered_colimits :=
(colimit : Π {J : Type v} [𝒥 : small_category J] [filtered.{v v} J] (F : J ⥤ C), cocone F)
(is_colimit : Π {J : Type v} [𝒥 : small_category J] [filtered.{v v} J] (F : J ⥤ C), is_colimit (colimit F) . obviously)

variable {C}

section
variables [has_colimits.{u v} C] {J : Type v} [𝒥 : small_category J] 
include 𝒥

def colimit.cocone (F : J ⥤ C) : cocone F := has_colimits.colimit.{u v} F
def colimit (F : J ⥤ C) := (colimit.cocone F).X
def colimit.ι (F : J ⥤ C) (j : J) : F j ⟶ colimit F := (colimit.cocone F).ι j
def colimit.universal_property (F : J ⥤ C) : is_colimit (colimit.cocone F) := 
has_colimits.is_colimit.{u v} C F

@[extensionality] def colimit.hom_ext {F : J ⥤ C} {c : cocone F}
  (f g : colimit F ⟶ c.X)
  (w_f : ∀ j, colimit.ι F j ≫ f = c.ι j)
  (w_g : ∀ j, colimit.ι F j ≫ g = c.ι j) : f = g :=
begin
  have p_f := (colimit.universal_property.{u v} F).uniq c f (by obviously),
  have p_g := (colimit.universal_property.{u v} F).uniq c g (by obviously),
  obviously,
end

end

end category_theory.limits