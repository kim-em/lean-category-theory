-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import .shape

open category_theory


namespace category_theory.universal

universes u v w

section

section shapes

/--
A `cospan Y Z`:
`Y₁ --ι₁--> X <--ι₂-- Y₂`
-/
structure cospan {C : Type u} [𝒞 : category.{u v} C] (Y₁ Y₂ : C) extends shape C :=
(ι₁ : Y₁ ⟶ X)
(ι₂ : Y₂ ⟶ X)

/--
A `cofan f`:
`X <--(π b)-- f b`
-/
structure cofan {C : Type u} [𝒞 : category.{u v} C] {β : Type v} (f : β → C) extends shape C :=
(ι : ∀ b, f b ⟶ X)

/--
A `cofork f g`:
```
              f
 X <--π-- Y <==== Z
              g
```            
-/
structure cofork {C : Type u} [𝒞 : category.{u v} C] {Y Z : C} (f g : Z ⟶ Y) extends shape C := 
(π : Y ⟶ X)
(w : f ≫ π = g ≫ π . obviously)

restate_axiom cofork.w
attribute [ematch] cofork.w_lemma

/-- 
A `cosquare p q`:
```
X  <--ι₁-- Y₁
↑          ↑
ι₂         r₁
|          |
Y₂ <--r₂-- Z
```
-/
structure cosquare {C : Type u} [𝒞 : category.{u v} C] {Y₁ Y₂ Z : C} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂)extends shape C :=
(ι₁ : Y₁ ⟶ X)
(ι₂ : Y₂ ⟶ X)
(w : r₁ ≫ ι₁ = r₂ ≫ ι₂ . obviously)

restate_axiom cosquare.w
attribute [ematch] cosquare.w_lemma

structure cocone {C : Type u} [𝒞 : category.{u v} C] {J : Type v} [small_category J] (F : J ↝ C) extends shape C :=
(ι : ∀ j : J, F j ⟶ X)
(w : ∀ {j j' : J} (f : j ⟶ j'), (F.map f) ≫ ι j' = ι j)

restate_axiom cocone.w
attribute [ematch] cocone.w_lemma

end shapes

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section initial
structure is_initial (t : C) :=
(desc : ∀ (s : C), t ⟶ s)
(uniq : ∀ (s : C) (m : t ⟶ s), m = desc s . obviously)

restate_axiom is_initial.uniq
attribute [ematch, back'] is_initial.uniq_lemma

@[extensionality] lemma is_initial.ext {X : C} (P Q : is_initial.{u v} X) : P = Q := 
begin cases P, cases Q, obviously, end

instance hom_to_initial_subsingleton (X' : C) (X : C) (B : is_initial.{u v} X') : subsingleton (X' ⟶ X) :=
begin
  fsplit, intros f g,
  rw B.uniq X f,
  rw B.uniq X g,
end

end initial

section binary_coproduct
structure is_binary_coproduct {Y Z : C} (t : cospan Y Z) :=
(desc : ∀ (s : cospan Y Z), t.X ⟶ s.X)
(fac₁ : ∀ (s : cospan Y Z), t.ι₁ ≫ (desc s) = s.ι₁ . obviously) 
(fac₂ : ∀ (s : cospan Y Z), t.ι₂ ≫ (desc s) = s.ι₂ . obviously) 
(uniq : ∀ (s : cospan Y Z) (m : t.X ⟶ s.X) (w₁ : t.ι₁ ≫ m = s.ι₁) (w₂ : t.ι₂ ≫ m = s.ι₂), m = desc s . obviously)

restate_axiom is_binary_coproduct.fac₁
attribute [simp,ematch] is_binary_coproduct.fac₁_lemma
restate_axiom is_binary_coproduct.fac₂
attribute [simp,ematch] is_binary_coproduct.fac₂_lemma
restate_axiom is_binary_coproduct.uniq
attribute [ematch, back'] is_binary_coproduct.uniq_lemma

@[extensionality] lemma is_binary_coproduct.ext {Y Z : C} {t : cospan Y Z} (P Q : is_binary_coproduct t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_binary_coproduct.uniq' {Y Z : C} {t : cospan Y Z} (h : is_binary_coproduct t) {X' : C} (m : t.X ⟶ X') : m = h.desc { X := X', ι₁ := t.ι₁ ≫ m, ι₂ := t.ι₂ ≫ m } :=
h.uniq { X := X', ι₁ := t.ι₁ ≫ m, ι₂ := t.ι₂ ≫ m } m (by obviously) (by obviously)

-- TODO provide alternative constructor using uniq' instead of uniq.

structure binary_coproduct (Y Z : C) extends t : cospan Y Z :=
(h : is_binary_coproduct t)

lemma is_binary_coproduct.univ {Y Z : C} {t : cospan Y Z} (h : is_binary_coproduct t) (s : cospan Y Z) (φ : t.X ⟶ s.X) : (t.ι₁ ≫ φ = s.ι₁ ∧ t.ι₂ ≫ φ = s.ι₂) ↔ (φ = h.desc s) :=
begin
obviously
end

def is_binary_coproduct.of_desc_univ {Y Z : C} {t : cospan Y Z}
  (desc : Π (s : cospan Y Z), t.X ⟶ s.X)
  (univ : Π (s : cospan Y Z) (φ : t.X ⟶ s.X), (t.ι₁ ≫ φ = s.ι₁ ∧ t.ι₂ ≫ φ = s.ι₂) ↔ (φ = desc s)) : is_binary_coproduct t :=
{ desc := desc,
  fac₁ := λ s, ((univ s (desc s)).mpr (eq.refl (desc s))).left, -- PROJECT automation
  fac₂ := λ s, ((univ s (desc s)).mpr (eq.refl (desc s))).right,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end } -- TODO should be easy to automate


end binary_coproduct

section coproduct
variables {β : Type v} {f : β → C} 

structure is_coproduct (t : cofan f) :=
(desc : ∀ (s : cofan f), t.X ⟶ s.X)
(fac  : ∀ (s : cofan f), ∀ b, t.ι b ≫ (desc s) = s.ι b . obviously) 
(uniq : ∀ (s : cofan f) (m : t.X ⟶ s.X) (w : ∀ b, t.ι b ≫ m = s.ι b), m = desc s . obviously)

restate_axiom is_coproduct.fac
attribute [simp,ematch] is_coproduct.fac_lemma
restate_axiom is_coproduct.uniq
attribute [ematch, back'] is_coproduct.uniq_lemma

@[extensionality] lemma is_coproduct.ext {t : cofan f} (P Q : is_coproduct t) : P = Q :=
begin cases P, cases Q, obviously end

instance is_coproduct_subsingleton {t : cofan f}  : subsingleton (is_coproduct t) := 
begin 
  fsplit, intros,
  apply is_coproduct.ext, -- obviously will do this after https://github.com/leanprover/mathlib/pull/269
end

lemma is_coproduct.uniq' {t : cofan f} (h : is_coproduct t) {X' : C} (m : t.X ⟶ X') : m = h.desc { X := X', ι := λ b, t.ι b ≫ m } :=
h.uniq { X := X', ι := λ b, t.ι b ≫ m } m (by obviously)

-- TODO provide alternative constructor using uniq' instead of uniq.

lemma is_coproduct.univ {t : cofan f} (h : is_coproduct t) (s : cofan f) (φ : t.X ⟶ s.X) : (∀ b, t.ι b ≫ φ = s.ι b) ↔ (φ = h.desc s) :=
begin
obviously
end

def is_coproduct.of_desc_univ {t :cofan f}
  (desc : Π (s : cofan f), t.X ⟶ s.X)
  (univ : Π (s : cofan f) (φ : t.X ⟶ s.X), (∀ b, t.ι b ≫ φ = s.ι b) ↔ (φ = desc s)) : is_coproduct t :=
{ desc := desc,
  fac  := λ s b, ((univ s (desc s)).mpr (eq.refl (desc s))) b,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end } -- TODO should be easy to automate

lemma homs_to_coproduct_ext {t : cofan f} (B : is_coproduct.{u v} t) {X : C} (f g : t.X ⟶ X) (w : ∀ b, t.ι b ≫ f = t.ι b ≫ g) : f = g :=
begin
  rw B.uniq' f,
  rw B.uniq' g,
  congr,
  ext,
  exact w x,
end

end coproduct


section coequalizer
variables {Y Z : C}
structure is_coequalizer {f g : Z ⟶ Y} (t : cofork f g) :=
(desc : ∀ (s : cofork f g), t.X ⟶ s.X)
(fac  : ∀ (s : cofork f g), t.π ≫ (desc s) = s.π . obviously)
(uniq : ∀ (s : cofork f g) (m : t.X ⟶ s.X) (w : t.π ≫ m = s.π), m = desc s . obviously)

restate_axiom is_coequalizer.fac
attribute [simp,ematch] is_coequalizer.fac_lemma
restate_axiom is_coequalizer.uniq
attribute [ematch, back'] is_coequalizer.uniq_lemma

@[extensionality] lemma is_coequalizer.ext {f g : Z ⟶ Y} {t : cofork f g} (P Q : is_coequalizer t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_coequalizer.epi {f g : Z ⟶ Y} {t : cofork f g} (h : is_coequalizer t) : epi (t.π) :=
{ left_cancellation := λ X' k l w, begin 
                                    let s : cofork f g := { X := X', π := t.π ≫ k }, 
                                    have uniq_k := h.uniq s k (by obviously),
                                    have uniq_l := h.uniq s l (by obviously),
                                    obviously,
                              end }

structure coequalizer (f g : Z ⟶ Y) extends t : cofork f g := 
(h : is_coequalizer t)

lemma is_coequalizer.univ {f g : Z ⟶ Y} {t : cofork f g} (h : is_coequalizer t) (s : cofork f g) (φ : t.X ⟶ s.X) : (t.π ≫ φ = s.π) ↔ (φ = h.desc s) :=
begin
obviously
end

def is_coequalizer.of_desc_univ {f g : Z ⟶ Y} {t : cofork f g}
  (desc : Π (s : cofork f g), t.X ⟶ s.X)
  (univ : Π (s : cofork f g) (φ : t.X ⟶ s.X), (t.π ≫ φ = s.π) ↔ (φ = desc s)) : is_coequalizer t :=
{ desc := desc,
  fac := λ s, ((univ s (desc s)).mpr (eq.refl (desc s))),
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

end coequalizer

section pushout
variables {Y₁ Y₂ Z : C}
structure is_pushout {r₁ : Z ⟶ Y₁} {r₂ : Z ⟶ Y₂} (t : cosquare r₁ r₂) :=
(desc : ∀ (s : cosquare r₁ r₂), t.X ⟶ s.X)
(fac₁ : ∀ (s : cosquare r₁ r₂), (t.ι₁ ≫ desc s) = s.ι₁ . obviously)
(fac₂ : ∀ (s : cosquare r₁ r₂), (t.ι₂ ≫ desc s) = s.ι₂ . obviously)
(uniq : ∀ (s : cosquare r₁ r₂) (m : t.X ⟶ s.X) (w₁ : (t.ι₁ ≫ m) = s.ι₁) (w₂ : (t.ι₂ ≫ m) = s.ι₂), m = desc s . obviously)

restate_axiom is_pushout.fac₁
attribute [simp,ematch] is_pushout.fac₁_lemma
restate_axiom is_pushout.fac₂
attribute [simp,ematch] is_pushout.fac₂_lemma
restate_axiom is_pushout.uniq
attribute [ematch, back'] is_pushout.uniq_lemma

@[extensionality] lemma is_pushout.ext {r₁ : Z ⟶ Y₁} {r₂ : Z ⟶ Y₂} {t : cosquare r₁ r₂} (P Q : is_pushout t) : P = Q :=
begin cases P, cases Q, obviously end

structure pushout (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) extends t : cosquare r₁ r₂ :=
(h : is_pushout t)

lemma is_pushout.univ {r₁ : Z ⟶ Y₁} {r₂ : Z ⟶ Y₂} {t : cosquare r₁ r₂} (h : is_pushout t) (s : cosquare r₁ r₂) (φ : t.X ⟶ s.X) : (t.ι₁ ≫ φ = s.ι₁ ∧ t.ι₂ ≫ φ = s.ι₂) ↔ (φ = h.desc s) :=
begin
obviously
end

def is_pushout.of_desc_univ {r₁ : Z ⟶ Y₁} {r₂ : Z ⟶ Y₂} {t : cosquare r₁ r₂}
  (desc : Π (s : cosquare r₁ r₂), t.X ⟶ s.X)
  (univ : Π (s : cosquare r₁ r₂) (φ : t.X ⟶ s.X), (t.ι₁ ≫ φ = s.ι₁ ∧ t.ι₂ ≫ φ = s.ι₂) ↔ (φ = desc s)) : is_pushout t :=
{ desc := desc,
  fac₁ := λ s, ((univ s (desc s)).mpr (eq.refl (desc s))).left,
  fac₂ := λ s, ((univ s (desc s)).mpr (eq.refl (desc s))).right,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }


end pushout

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

class has_initial_object :=
(initial    : C)
(is_initial : is_initial.{u v} initial . obviously)

class has_binary_coproducts :=
(coprod    : Π (Y Z : C), cospan Y Z)
(is_binary_coproduct : Π (Y Z : C), is_binary_coproduct (coprod Y Z) . obviously)

class has_coproducts :=
(coprod : Π {β : Type v} (f : β → C), cofan.{u v} f)
(is_coproduct : Π {β : Type v} (f : β → C), is_coproduct (coprod f) . obviously)

class has_coequalizers :=
(coequalizer : Π {Y Z : C} (f g : Y ⟶ Z), cofork f g)
(is_coequalizer : Π {Y Z : C} (f g : Y ⟶ Z), is_coequalizer (coequalizer f g) . obviously)

class has_pushouts :=
(pushout : Π {Y₁ Y₂ Z : C} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂), cosquare r₁ r₂)
(is_pushout : Π {Y₁ Y₂ Z : C} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂), is_pushout (pushout r₁ r₂) . obviously)

class has_colimits :=
(colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ↝ C), cocone F)
(is_colimit : Π {J : Type v} [𝒥 : small_category J] (F : J ↝ C), is_colimit (colimit F) . obviously)


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

end


end category_theory.universal

