-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.shape

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section product
variables {β : Type v} {f : β → C} 

structure is_product (t : fan f) :=
(lift : ∀ (s : fan f), s.X ⟶ t.X)
(fac  : ∀ (s : fan f), ∀ b, (lift s) ≫ t.π b = s.π b . obviously) 
(uniq : ∀ (s : fan f) (m : s.X ⟶ t.X) (w : ∀ b, m ≫ t.π b = s.π b), m = lift s . obviously)

restate_axiom is_product.fac
attribute [simp,search] is_product.fac_lemma
restate_axiom is_product.uniq
attribute [search, back'] is_product.uniq_lemma

@[extensionality] lemma is_product.ext {t : fan f} (P Q : is_product t) : P = Q :=
begin cases P, cases Q, obviously end

instance is_product_subsingleton {t : fan f}  : subsingleton (is_product t) := by obviously

lemma is_product.uniq' {t : fan f} (h : is_product t) {X' : C} (m : X' ⟶ t.X) : m = h.lift { X := X', π := λ b, m ≫ t.π b } :=
h.uniq { X := X', π := λ b, m ≫ t.π b } m (by obviously)

-- TODO provide alternative constructor using uniq' instead of uniq.

lemma is_product.univ {t : fan f} (h : is_product t) (s : fan f) (φ : s.X ⟶ t.X) : (∀ b, φ ≫ t.π b = s.π b) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_product.of_lift_univ {t : fan f}
  (lift : Π (s : fan f), s.X ⟶ t.X)
  (univ : Π (s : fan f) (φ : s.X ⟶ t.X), (∀ b, φ ≫ t.π b = s.π b) ↔ (φ = lift s)) : is_product t :=
{ lift := lift,
  fac  := λ s b, ((univ s (lift s)).mpr (eq.refl (lift s))) b,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end } -- TODO should be easy to automate

end product


section coproduct
variables {β : Type v} {f : β → C} 

structure is_coproduct (t : cofan f) :=
(desc : ∀ (s : cofan f), t.X ⟶ s.X)
(fac  : ∀ (s : cofan f), ∀ b, t.ι b ≫ (desc s) = s.ι b . obviously) 
(uniq : ∀ (s : cofan f) (m : t.X ⟶ s.X) (w : ∀ b, t.ι b ≫ m = s.ι b), m = desc s . obviously)

restate_axiom is_coproduct.fac
attribute [simp,search] is_coproduct.fac_lemma
restate_axiom is_coproduct.uniq
attribute [search, back'] is_coproduct.uniq_lemma

@[extensionality] lemma is_coproduct.ext {t : cofan f} (P Q : is_coproduct t) : P = Q :=
begin cases P, cases Q, obviously end

instance is_coproduct_subsingleton {t : cofan f}  : subsingleton (is_coproduct t) := by obviously

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

variable (C)

class has_products :=
(prod : Π {β : Type v} (f : β → C), fan.{u v} f)
(is_product : Π {β : Type v} (f : β → C), is_product (prod f) . obviously)

class has_coproducts :=
(coprod : Π {β : Type v} (f : β → C), cofan.{u v} f)
(is_coproduct : Π {β : Type v} (f : β → C), is_coproduct (coprod f) . obviously)

variable {C}

section
variables [has_products.{u v} C] {β : Type v} 

def pi.fan (f : β → C) := has_products.prod.{u v} f
def pi (f : β → C) : C := (pi.fan f).X
def pi.π (f : β → C) (b : β) : pi f ⟶ f b := (pi.fan f).π b
def pi.universal_property (f : β → C) : is_product (pi.fan f) := has_products.is_product.{u v} C f
def pi.lift (f : β → C) (g : fan f) := (pi.universal_property f).lift g

@[extensionality] lemma pi.hom_ext (f : β → C) {X : C} (g h : X ⟶ pi f) (w : ∀ b, g ≫ pi.π f b = h ≫ pi.π f b) : g = h :=
begin
  rw (pi.universal_property f).uniq' g,
  rw (pi.universal_property f).uniq' h,
  congr,
  ext,
  exact w x,
end

lemma pi.components_eq (f : β → C) {X : C} {g h : X ⟶ pi f} (e : g = h) (b : β) : g ≫ pi.π f b = h ≫ pi.π f b := by subst e

@[simp] def pi.fan_π (f : β → C) (b : β) : (pi.fan f).π b = @pi.π C _ _ _ f b := rfl
@[simp] def pi.lift_π (f : β → C) (g : fan f) (b : β) : (pi.universal_property f).lift g ≫ pi.π f b = g.π b :=
(pi.universal_property f).fac g b

def pi.of_components {f : β → C} {P : C} (p : Π b, P ⟶ f b) : P ⟶ pi f :=
(pi.universal_property f).lift ⟨ ⟨ P ⟩, p ⟩

@[simp,search] def pi.of_components_π {f : β → C} {P : C} (p : Π b, P ⟶ f b) (b : β) : pi.of_components p ≫ pi.π f b = p b :=
begin
  dsimp [pi.of_components],
  rw ← pi.fan_π f,
  rw (pi.universal_property f).fac,
end

def pi.map {α : Type v} {f : α → C} {g : β → C} (h : β → α) (k : Π b, f (h b) ⟶ g b) : (pi f) ⟶ (pi g) :=
pi.of_components (λ b, pi.π f (h b) ≫ k b) 

@[simp] def pi.of_components_map 
  {α : Type v} {f : α → C} {g : β → C} {P : C} (p : Π b, P ⟶ f b) (h : β → α) (k : Π b, f (h b) ⟶ g b) :
  pi.of_components p ≫ pi.map h k = pi.of_components (λ b, p (h b) ≫ k b) :=
begin
  obviously,
end

end

end category_theory.limits
