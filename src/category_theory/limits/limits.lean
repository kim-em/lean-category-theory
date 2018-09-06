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

class is_limit {F : J ⥤ C} (t : cone F) :=
(lift : ∀ (s : cone F), s.X ⟶ t.X)
(fac'  : ∀ (s : cone F) (j : J), (lift s ≫ t.π j) = s.π j . obviously)
(uniq' : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, (m ≫ t.π j) = s.π j), m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp,search] is_limit.fac
restate_axiom is_limit.uniq'
attribute [search,back'] is_limit.uniq

@[extensionality] lemma is_limit.ext {F : J ⥤ C} {t : cone F} (P Q : is_limit t) : P = Q :=
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously end

lemma is_limit.univ {F : J ⥤ C} {t : cone F} [is_limit t] (s : cone F) (φ : s.X ⟶ t.X) : 
  (∀ j, φ ≫ t.π j = s.π j) ↔ (φ = is_limit.lift t s) :=
by obviously

def is_limit.of_lift_univ {F : J ⥤ C} {t : cone F}
  (lift : Π (s : cone F), s.X ⟶ t.X)
  (univ : Π (s : cone F) (φ : s.X ⟶ t.X), (∀ j : J, (φ ≫ t.π j) = s.π j) ↔ (φ = lift s)) : is_limit t :=
{ lift := lift,
  fac'  := λ s j, ((univ s (lift s)).mpr (eq.refl (lift s))) j,
  uniq' := begin obviously, apply univ_s_m.mp, obviously, end }

end limit


section colimit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

class is_colimit {F : J ⥤ C} (t : cocone F) :=
(desc : ∀ (s : cocone F), t.X ⟶ s.X)
(fac'  : ∀ (s : cocone F) (j : J), (t.ι j ≫ desc s) = s.ι j . obviously)
(uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, (t.ι j ≫ m) = s.ι j), m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp,search] is_colimit.fac
restate_axiom is_colimit.uniq'
attribute [search,back'] is_colimit.uniq

@[extensionality] lemma is_colimit.ext {F : J ⥤ C} {t : cocone F} (P Q : is_colimit t) : P = Q :=
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously end

lemma is_colimit.univ {F : J ⥤ C} {t : cocone F} [is_colimit t] (s : cocone F) (φ : t.X ⟶ s.X) : 
  (∀ j, t.ι j ≫ φ = s.ι j) ↔ (φ = is_colimit.desc t s) :=
by obviously

def is_colimit.of_desc_univ {F : J ⥤ C} {t : cocone F}
  (desc : Π (s : cocone F), t.X ⟶ s.X)
  (univ : Π (s : cocone F) (φ : t.X ⟶ s.X), (∀ j : J, (t.ι j ≫ φ) = s.ι j) ↔ (φ = desc s)) : is_colimit t :=
{ desc := desc,
  fac'  := λ s j, ((univ s (desc s)).mpr (eq.refl (desc s))) j,
  uniq' := begin obviously, apply univ_s_m.mp, obviously, end }

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
instance limit.universal_property (F : J ⥤ C) : is_limit (limit.cone F) := 
has_limits.is_limit.{u v} C F

def limit.lift (F : J ⥤ C) (c : cone F) : c.X ⟶ limit F := is_limit.lift _ c

-- @[simp] def limit.universal_property_lift (F : J ⥤ C) (c : cone F) : (limit.universal_property F).lift c = limit.lift F c := rfl
@[simp] def limit.lift_π (F : J ⥤ C) (c : cone F) (j : J) : limit.lift F c ≫ limit.π F j = c.π j :=
is_limit.fac _ c j

-- FIXME why the @?
@[simp] lemma limit.cone_π (F : J ⥤ C) (j : J) : (limit.cone F).π j = (@limit.π C _ _ J _ F j) := rfl

-- TODO needs a home
def cone.pullback {F : J ⥤ C} (A : cone F) {X : C} (f : X ⟶ A.X) : cone F :=
{ X := X,
  π := λ j, f ≫ A.π j }

-- lemma limit.pullback_lift (F : J ⥤ C) (c : cone F) {X : C} (f : X ⟶ c.X) : f ≫ limit.lift F c = limit.lift F (c.pullback f) := sorry

def limit.map (F G : J ⥤ C) (α : F ⟹ G) : limit F ⟶ limit G :=
is_limit.lift _ { X := _, π := λ j, limit.π F j ≫ α j }

section
variables {K : Type v} [𝒦 : small_category K]
include 𝒦

def limit.pre (F : J ⥤ C) (E : K ⥤ J) : limit F ⟶ limit (E ⋙ F) :=
@is_limit.lift _ _ _ _ _ (limit.cone (E ⋙ F)) _ { X := limit F, π := λ k, limit.π F (E k) }
end

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_limits.{u v} D]
include 𝒟 

def limit.post (F : J ⥤ C) (G : C ⥤ D) : G (limit F) ⟶ limit (F ⋙ G) :=
@is_limit.lift _ _ _ _ _ (limit.cone (F ⋙ G)) _ { X := _, π := λ j, G.map (limit.π F j) }
end

@[extensionality] def limit.hom_ext {F : J ⥤ C} {c : cone F}
  (f g : c.X ⟶ limit F)
  (w_f : ∀ j, f ≫ limit.π F j = c.π j)
  (w_g : ∀ j, g ≫ limit.π F j = c.π j) : f = g :=
begin
  have p_f := is_limit.uniq _ c f (by obviously),
  have p_g := is_limit.uniq _ c g (by obviously),
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
instance colimit.universal_property (F : J ⥤ C) : is_colimit (colimit.cocone F) := 
has_colimits.is_colimit.{u v} C F

def colimit.desc (F : J ⥤ C) (c : cocone F) : colimit F ⟶ c.X := is_colimit.desc _ c

section
variables {K : Type v} [𝒦 : small_category K]
include 𝒦

def colimit.pre (F : J ⥤ C) (E : K ⥤ J) : colimit (E ⋙ F) ⟶ colimit F :=
@is_colimit.desc _ _ _ _ _ (colimit.cocone (E ⋙ F)) _ { X := colimit F, ι := λ k, colimit.ι F (E k) }
end

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_colimits.{u v} D]
include 𝒟

def colimit.post (F : J ⥤ C) (G : C ⥤ D) : colimit (F ⋙ G) ⟶ G (colimit F) :=
@is_colimit.desc _ _ _ _ _ (colimit.cocone (F ⋙ G)) _ { X := _, ι := λ j, G.map (colimit.ι F j) }
end

@[extensionality] def colimit.hom_ext {F : J ⥤ C} {c : cocone F}
  (f g : colimit F ⟶ c.X)
  (w_f : ∀ j, colimit.ι F j ≫ f = c.ι j)
  (w_g : ∀ j, colimit.ι F j ≫ g = c.ι j) : f = g :=
begin
  have p_f := is_colimit.uniq _ c f (by obviously),
  have p_g := is_colimit.uniq _ c g (by obviously),
  obviously,
end

end

end category_theory.limits