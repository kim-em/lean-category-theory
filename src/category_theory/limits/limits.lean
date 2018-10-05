-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.discrete_category
import category_theory.whiskering
import category_theory.universal.cones

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
(fac'  : ∀ (s : cone F) (j : J), (lift s ≫ t.π j) = s.π j . obviously)
(uniq' : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, (m ≫ t.π j) = s.π j), m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp,search] is_limit.fac
restate_axiom is_limit.uniq'
attribute [search,back'] is_limit.uniq

@[extensionality] lemma is_limit.ext {F : J ⥤ C} {t : cone F} (P Q : is_limit t) : P = Q :=
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously end

lemma is_limit.univ {F : J ⥤ C} {t : cone F} [h : is_limit t] (s : cone F) (φ : s.X ⟶ t.X) : 
  (∀ j, φ ≫ t.π j = s.π j) ↔ (φ = is_limit.lift h s) :=
by obviously

def is_limit.of_lift_univ {F : J ⥤ C} {t : cone F}
  (lift : Π (s : cone F), s.X ⟶ t.X)
  (univ : Π (s : cone F) (φ : s.X ⟶ t.X), (∀ j : J, (φ ≫ t.π j) = s.π j) ↔ (φ = lift s)) : is_limit t :=
{ lift := lift,
  fac'  := λ s j, ((univ s (lift s)).mpr (eq.refl (lift s))) j }

end limit


section colimit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

structure is_colimit {F : J ⥤ C} (t : cocone F) :=
(desc : ∀ (s : cocone F), t.X ⟶ s.X)
(fac'  : ∀ (s : cocone F) (j : J), (t.ι j ≫ desc s) = s.ι j . obviously)
(uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, (t.ι j ≫ m) = s.ι j), m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp,search] is_colimit.fac
restate_axiom is_colimit.uniq'
attribute [search,back'] is_colimit.uniq

@[extensionality] lemma is_colimit.ext {F : J ⥤ C} {t : cocone F} (P Q : is_colimit t) : P = Q :=
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously end

lemma is_colimit.univ {F : J ⥤ C} {t : cocone F} [h : is_colimit t] (s : cocone F) (φ : t.X ⟶ s.X) : 
  (∀ j, t.ι j ≫ φ = s.ι j) ↔ (φ = is_colimit.desc h s) :=
by obviously

def is_colimit.of_desc_univ {F : J ⥤ C} {t : cocone F}
  (desc : Π (s : cocone F), t.X ⟶ s.X)
  (univ : Π (s : cocone F) (φ : t.X ⟶ s.X), (∀ j : J, (t.ι j ≫ φ) = s.ι j) ↔ (φ = desc s)) : is_colimit t :=
{ desc := desc,
  fac'  := λ s j, ((univ s (desc s)).mpr (eq.refl (desc s))) j }

end colimit

variable (C)

class has_limits :=
(limit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), cone F)
(is_limit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), is_limit (limit F) . obviously)


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

@[simp] def limit.lift_π (F : J ⥤ C) (c : cone F) (j : J) : limit.lift F c ≫ limit.π F j = c.π j :=
is_limit.fac _ c j

@[simp] lemma limit.cone_π (F : J ⥤ C) (j : J) : (limit.cone F).π j = (@limit.π C _ _ J _ F j) := rfl

def limit.cone_morphism (F : J ⥤ C) (c : cone F) : cone_morphism c (limit.cone F) := 
{ hom := (limit.lift F) c }

@[simp] lemma limit.cone_morphism_hom {F : J ⥤ C} (c : cone F) : (limit.cone_morphism F c).hom = limit.lift F c := rfl
@[simp] lemma limit.cone_morphism_π {F : J ⥤ C} (c : cone F) (j : J) : (limit.cone_morphism F c).hom ≫ (limit.π F j) = c.π j :=
by erw is_limit.fac

-- TODO needs a home
def cone.precompose {F : J ⥤ C} (A : cone F) {X : C} (f : X ⟶ A.X) : cone F :=
{ X := X,
  π := λ j, f ≫ A.π j }


@[extensionality] def limit.hom_ext {F : J ⥤ C} {X : C}
  (f g : X ⟶ limit F)
  (w : ∀ j, f ≫ limit.π F j = g ≫ limit.π F j) : f = g :=
begin
  let c : cone F := { X := X, π := λ j, f ≫ limit.π F j },
  have p_f := (limit.universal_property F).uniq c f (by obviously),
  have p_g := (limit.universal_property F).uniq c g (by obviously),
  obviously
end

lemma limit.precompose_lift (F : J ⥤ C) (c : cone F) {X : C} (f : X ⟶ c.X) : 
  limit.lift F (c.precompose f) = f ≫ limit.lift F c :=
by obviously

/-- `limit F` is functorial in `F`. -/
@[simp] def lim : (J ⥤ C) ⥤ C := 
{ obj := limit,
  map' := λ F F' t, limit.lift F' $
    { X := limit F, π := λ j, limit.π F j ≫ t j } }.
 
@[simp] lemma lim_map_π {F G : J ⥤ C} (α : F ⟹ G) (j : J) : lim.map α ≫ limit.π G j = limit.π F j ≫ α j :=
by erw is_limit.fac

@[simp] def limit.lift_map {F G : J ⥤ C} (c : cone F) (α : F ⟹ G) : 
  limit.lift F c ≫ lim.map α = limit.lift G { X := c.X, π := λ j, c.π j ≫ α j } := -- should this cone have a name?
by obviously

section
variables {K : Type v} [𝒦 : small_category K]
include 𝒦

def limit.pre (F : J ⥤ C) (E : K ⥤ J) : limit F ⟶ limit (E ⋙ F) :=
limit.lift (E ⋙ F) { X := limit F, π := λ k, limit.π F (E k) }

@[simp,search] lemma limit.pre_π (F : J ⥤ C) (E : K ⥤ J) (k : K) : 
  limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E k) :=
by erw is_limit.fac

@[simp] def limit.lift_pre {F : J ⥤ C} (c : cone F) (E : K ⥤ J) :
  limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) { X := c.X, π := λ k, c.π (E k) } := -- should this cone have a name?
by obviously

def limit.map_pre {F G : J ⥤ C} (α : F ⟹ G) (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_on_left E α) :=
by obviously

@[simp] lemma limit.pre_pre {L : Type v} [small_category L] (F : J ⥤ C) (E : K ⥤ J) (D : L ⥤ K) :
  limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) :=
by obviously
end

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_limits.{u v} D]
include 𝒟 

def limit.post (F : J ⥤ C) (G : C ⥤ D) : G (limit F) ⟶ limit (F ⋙ G) :=
limit.lift (F ⋙ G) { X := _, π := λ j, G.map (limit.π F j) }

@[simp,search] lemma limit.post_π (F : J ⥤ C) (G : C ⥤ D) (j : J) : 
  limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) :=
by erw is_limit.fac

@[simp] def limit.lift_post {F : J ⥤ C} (c : cone F) (G : C ⥤ D) :
  G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.map_cone c) := -- should this cone have a name?
by obviously

def limit.map_post {F G : J ⥤ C} (α : F ⟹ G) (H : C ⥤ D) :
/- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
   H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
  H.map (lim.map α) ≫ limit.post G H = limit.post F H ≫ lim.map (whisker_on_right α H) :=
by obviously

def limit.pre_post {K : Type v} [small_category K] (F : J ⥤ C) (E : K ⥤ J) (G : C ⥤ D) :
/- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs -/
/- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or -/
  G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E :=
by obviously.

@[simp] def limit.post_post {E : Type u} [category.{u v} E] [has_limits.{u v} E] (F : J ⥤ C) (G : C ⥤ D) (H : D ⥤ E):
/- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) vs -/
/- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H)) or -/
  H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) :=
by obviously
end

end

variable (C)

class has_colimits :=
(colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), cocone F)
(is_colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ⥤ C), is_colimit (colimit F) . obviously)


variable {C}

section
variables [has_colimits.{u v} C] {J : Type v} [𝒥 : small_category J] 
include 𝒥

def colimit.cocone (F : J ⥤ C) : cocone F := has_colimits.colimit.{u v} F
def colimit (F : J ⥤ C) := (colimit.cocone F).X
def colimit.ι (F : J ⥤ C) (j : J) : F j ⟶ colimit F := (colimit.cocone F).ι j
def colimit.universal_property (F : J ⥤ C) : is_colimit (colimit.cocone F) := 
has_colimits.is_colimit.{u v} C F

def colimit.desc (F : J ⥤ C) (c : cocone F) : colimit F ⟶ c.X := (colimit.universal_property F).desc c

section
variables {K : Type v} [𝒦 : small_category K]
include 𝒦

def colimit.pre (F : J ⥤ C) (E : K ⥤ J) : colimit (E ⋙ F) ⟶ colimit F :=
colimit.desc (E ⋙ F) { X := colimit F, ι := λ k, colimit.ι F (E k) }
end

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_colimits.{u v} D]
include 𝒟

def colimit.post (F : J ⥤ C) (G : C ⥤ D) : colimit (F ⋙ G) ⟶ G (colimit F) :=
colimit.desc (F ⋙ G) { X := _, ι := λ j, G.map (colimit.ι F j) }
end

@[extensionality] def colimit.hom_ext {F : J ⥤ C} {c : cocone F}
  (f g : colimit F ⟶ c.X)
  (w_f : ∀ j, colimit.ι F j ≫ f = c.ι j)
  (w_g : ∀ j, colimit.ι F j ≫ g = c.ι j) : f = g :=
begin
  have p_f := (colimit.universal_property F).uniq c f (by obviously),
  have p_g := (colimit.universal_property F).uniq c g (by obviously),
  obviously,
end

end

end category_theory.limits