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

class is_product (t : fan f) :=
(lift : ∀ (s : fan f), s.X ⟶ t.X)
(fac'  : ∀ (s : fan f), ∀ b, (lift s) ≫ t.π b = s.π b . obviously) 
(uniq' : ∀ (s : fan f) (m : s.X ⟶ t.X) (w : ∀ b, m ≫ t.π b = s.π b), m = lift s . obviously)

restate_axiom is_product.fac'
attribute [simp,search] is_product.fac
restate_axiom is_product.uniq'
attribute [search,back'] is_product.uniq

@[extensionality] lemma is_product.ext {t : fan f} (P Q : is_product t) : P = Q :=
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously end

instance is_product_subsingleton {t : fan f}  : subsingleton (is_product t) := by obviously

lemma is_product.uniq'' {t : fan f} [is_product t] {X' : C} (m : X' ⟶ t.X) : m = is_product.lift t { X := X', π := λ b, m ≫ t.π b } :=
is_product.uniq t { X := X', π := λ b, m ≫ t.π b } m (by obviously)

-- TODO provide alternative constructor using uniq'' instead of uniq'.

lemma is_product.univ {t : fan f} [is_product t] (s : fan f) (φ : s.X ⟶ t.X) : (∀ b, φ ≫ t.π b = s.π b) ↔ (φ = is_product.lift t s) :=
begin
obviously
end

def is_product.of_lift_univ {t : fan f}
  (lift : Π (s : fan f), s.X ⟶ t.X)
  (univ : Π (s : fan f) (φ : s.X ⟶ t.X), (∀ b, φ ≫ t.π b = s.π b) ↔ (φ = lift s)) : is_product t :=
{ lift := lift,
  fac'  := λ s b, ((univ s (lift s)).mpr (eq.refl (lift s))) b,
  uniq' := begin obviously, apply univ_s_m.mp, obviously, end }

end product


section coproduct
variables {β : Type v} {f : β → C} 

class is_coproduct (t : cofan f) :=
(desc : ∀ (s : cofan f), t.X ⟶ s.X)
(fac'  : ∀ (s : cofan f), ∀ b, t.ι b ≫ (desc s) = s.ι b . obviously) 
(uniq' : ∀ (s : cofan f) (m : t.X ⟶ s.X) (w : ∀ b, t.ι b ≫ m = s.ι b), m = desc s . obviously)

restate_axiom is_coproduct.fac'
attribute [simp,search] is_coproduct.fac
restate_axiom is_coproduct.uniq'
attribute [search, back'] is_coproduct.uniq

@[extensionality] lemma is_coproduct.ext {t : cofan f} (P Q : is_coproduct t) : P = Q :=
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously end

instance is_coproduct_subsingleton {t : cofan f}  : subsingleton (is_coproduct t) := by obviously

lemma is_coproduct.uniq'' {t : cofan f} [is_coproduct t] {X' : C} (m : t.X ⟶ X') : m = is_coproduct.desc t { X := X', ι := λ b, t.ι b ≫ m } :=
is_coproduct.uniq t { X := X', ι := λ b, t.ι b ≫ m } m (by obviously)

-- TODO provide alternative constructor using uniq'' instead of uniq'.

lemma is_coproduct.univ {t : cofan f} [is_coproduct t] (s : cofan f) (φ : t.X ⟶ s.X) : (∀ b, t.ι b ≫ φ = s.ι b) ↔ (φ = is_coproduct.desc t s) :=
begin
obviously
end

def is_coproduct.of_desc_univ {t :cofan f}
  (desc : Π (s : cofan f), t.X ⟶ s.X)
  (univ : Π (s : cofan f) (φ : t.X ⟶ s.X), (∀ b, t.ι b ≫ φ = s.ι b) ↔ (φ = desc s)) : is_coproduct t :=
{ desc := desc,
  fac'  := λ s b, ((univ s (desc s)).mpr (eq.refl (desc s))) b,
  uniq' := begin obviously, apply univ_s_m.mp, obviously, end }

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
instance pi.universal_property (f : β → C) : is_product (pi.fan f) := has_products.is_product.{u v} C f
def pi.lift (f : β → C) (g : fan f) := is_product.lift (pi.fan f) g

lemma pi.components_eq (f : β → C) {X : C} {g h : X ⟶ pi f} (e : g = h) (b : β) : g ≫ pi.π f b = h ≫ pi.π f b := by subst e

@[simp] def pi.fan_π (f : β → C) (b : β) : (pi.fan f).π b = @pi.π C _ _ _ f b := rfl
@[simp] def pi.lift_π (f : β → C) (g : fan f) (b : β) : pi.lift f g ≫ pi.π f b = g.π b :=
is_product.fac _ g b

def pi.of_components {f : β → C} {P : C} (p : Π b, P ⟶ f b) : P ⟶ pi f :=
is_product.lift _ ⟨ ⟨ P ⟩, p ⟩

def pi.shuffle {α} {f : α → C} (h : β → α) : pi f ⟶ pi (f ∘ h) :=
pi.of_components (λ g, pi.π f (h g))

def pi.map {α : Type v} {f : α → C} {g : β → C} (h : β → α) (k : Π b, f (h b) ⟶ g b) : (pi f) ⟶ (pi g) :=
pi.of_components (λ b, pi.π f (h b) ≫ k b) 

-- TODO lemmas describing shuffle: shuffle_π, of_components_shuffle, map_shuffle, shuffle_shuffle

@[simp,search] def pi.of_components_π {f : β → C} {P : C} (p : Π b, P ⟶ f b) (b : β) : pi.of_components p ≫ pi.π f b = p b :=
begin
  dsimp [pi.of_components],
  rw ← pi.fan_π f,
  rw is_product.fac (pi.fan f),
end

@[simp] def pi.map_π {α : Type v} {f : α → C} {g : β → C} (h : β → α) (k : Π b, f (h b) ⟶ g b) (b : β) : pi.map h k ≫ pi.π g b = pi.π f (h b) ≫ k b :=
by erw is_product.fac

@[extensionality] lemma pi.hom_ext (f : β → C) {X : C} (g h : X ⟶ pi f) (w : ∀ b, g ≫ pi.π f b = h ≫ pi.π f b) : g = h :=
begin
  rw is_product.uniq'' g,
  rw is_product.uniq'' h,
  congr,
  ext,
  exact w x,
end

@[simp] def pi.of_components_map 
  {α : Type v} {f : α → C} {g : β → C} {P : C} (p : Π b, P ⟶ f b) (h : β → α) (k : Π b, f (h b) ⟶ g b) :
  pi.of_components p ≫ pi.map h k = pi.of_components (λ b, p (h b) ≫ k b) :=
begin
  obviously,
end

@[simp] def pi.map_map  {α β γ : Type v} {fα : α → C} {fβ : β → C} {fγ : γ → C} 
  (hα : β → α) (hβ : γ → β) (kα : Π b, fα (hα b) ⟶ fβ b) (kβ : Π g, fβ (hβ g) ⟶ fγ g) :
  pi.map hα kα ≫ pi.map hβ kβ = pi.map (hα ∘ hβ) (λ g, kα (hβ g) ≫ kβ g)
:= by obviously

end

-- TODO coproducts

end category_theory.limits
