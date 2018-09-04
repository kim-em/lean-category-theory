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

variable (C)

class has_products :=
(prod : Π {β : Type v} (f : β → C), fan.{u v} f)
(is_product : Π {β : Type v} (f : β → C), is_product (prod f) . obviously)


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