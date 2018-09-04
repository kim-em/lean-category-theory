-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.shape

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section binary_product
structure is_binary_product {Y Z : C} (t : span Y Z) :=
(lift : ∀ (s : span Y Z), s.X ⟶ t.X)
(fac₁ : ∀ (s : span Y Z), (lift s) ≫ t.π₁ = s.π₁ . obviously) 
(fac₂ : ∀ (s : span Y Z), (lift s) ≫ t.π₂ = s.π₂ . obviously) 
(uniq : ∀ (s : span Y Z) (m : s.X ⟶ t.X) (w₁ : m ≫ t.π₁ = s.π₁) (w₂ : m ≫ t.π₂ = s.π₂), m = lift s . obviously)

restate_axiom is_binary_product.fac₁
attribute [simp,search] is_binary_product.fac₁_lemma
restate_axiom is_binary_product.fac₂
attribute [simp,search] is_binary_product.fac₂_lemma
restate_axiom is_binary_product.uniq
attribute [search,back'] is_binary_product.uniq_lemma

@[extensionality] lemma is_binary_product.ext {Y Z : C} {t : span Y Z} (P Q : is_binary_product t) : P = Q :=
begin cases P, cases Q, obviously end

instance {Y Z : C} {t : span Y Z} : subsingleton (is_binary_product t) := by obviously

lemma is_binary_product.uniq' {Y Z : C} {t : span Y Z} (h : is_binary_product t) {X' : C} (m : X' ⟶ t.X) : 
  m = h.lift { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } :=
h.uniq { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } m (by obviously) (by obviously)

-- TODO provide alternative constructor using uniq' instead of uniq?

lemma is_binary_product.univ {Y Z : C} {t : span Y Z} (h : is_binary_product t) (s : span Y Z) (φ : s.X ⟶ t.X) : (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
begin
  obviously
end

def is_binary_product.of_lift_univ {Y Z : C} {t : span Y Z}
  (lift : Π (s : span Y Z), s.X ⟶ t.X)
  (univ : Π (s : span Y Z) (φ : s.X ⟶ t.X), (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = lift s)) : is_binary_product t :=
{ lift := lift,
  fac₁ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).left, -- PROJECT automation
  fac₂ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).right,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end } -- TODO should be easy to automate

end binary_product

section binary_coproduct
structure is_binary_coproduct {Y Z : C} (t : cospan Y Z) :=
(desc : ∀ (s : cospan Y Z), t.X ⟶ s.X)
(fac₁ : ∀ (s : cospan Y Z), t.ι₁ ≫ (desc s) = s.ι₁ . obviously) 
(fac₂ : ∀ (s : cospan Y Z), t.ι₂ ≫ (desc s) = s.ι₂ . obviously) 
(uniq : ∀ (s : cospan Y Z) (m : t.X ⟶ s.X) (w₁ : t.ι₁ ≫ m = s.ι₁) (w₂ : t.ι₂ ≫ m = s.ι₂), m = desc s . obviously)

restate_axiom is_binary_coproduct.fac₁
attribute [simp,search] is_binary_coproduct.fac₁_lemma
restate_axiom is_binary_coproduct.fac₂
attribute [simp,search] is_binary_coproduct.fac₂_lemma
restate_axiom is_binary_coproduct.uniq
attribute [search, back'] is_binary_coproduct.uniq_lemma

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

variable (C)

class has_binary_products :=
(prod    : Π (Y Z : C), span Y Z)
(is_binary_product : Π (Y Z : C), is_binary_product (prod Y Z) . obviously)

class has_binary_coproducts :=
(coprod    : Π (Y Z : C), cospan Y Z)
(is_binary_coproduct : Π (Y Z : C), is_binary_coproduct (coprod Y Z) . obviously)

variable {C}

section 
variables [has_binary_products.{u v} C] 

def prod.span (Y Z : C) := has_binary_products.prod.{u v} Y Z
def prod (Y Z : C) : C := (prod.span Y Z).X
def prod.π₁ (Y Z : C) : prod Y Z ⟶ Y := (prod.span Y Z).π₁
def prod.π₂ (Y Z : C) : prod Y Z ⟶ Z := (prod.span Y Z).π₂
@[back] def prod.universal_property (Y Z : C) : is_binary_product (prod.span Y Z) :=
has_binary_products.is_binary_product.{u v} C Y Z
def prod.pair {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : P ⟶ (prod Q R) :=
(prod.universal_property Q R).lift ⟨ ⟨ P ⟩, f, g ⟩

def prod.map {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) : (prod P R) ⟶ (prod Q S) :=
prod.pair (prod.π₁ P R ≫ f) (prod.π₂ P R ≫ g)

@[simp,search] lemma prod.pair_π₁ {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : prod.pair f g ≫ prod.π₁ Q R = f := 
(prod.universal_property.{u v} Q R).fac₁_lemma { X := P, π₁ := f, π₂ := g }
@[simp,search] lemma prod.pair_π₂ {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : prod.pair f g ≫ prod.π₂ Q R = g :=
(prod.universal_property.{u v} Q R).fac₂_lemma { X := P, π₁ := f, π₂ := g }

@[extensionality] def prod.hom_ext (Y Z : C) (X : C) 
  (f g : X ⟶ prod Y Z) 
  (w₁ : f ≫ prod.π₁ Y Z = g ≫ prod.π₁ Y Z) 
  (w₂ : f ≫ prod.π₂ Y Z = g ≫ prod.π₂ Y Z) : f = g := 
begin 
  rw (prod.universal_property Y Z).uniq' f,
  rw (prod.universal_property Y Z).uniq' g,
  congr ; assumption,
end

end

end category_theory.limits
