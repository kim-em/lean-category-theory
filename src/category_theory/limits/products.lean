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
-- def pi.lift (f : β → C) (g : fan f) := is_product.lift (pi.fan f) g

-- lemma pi.components_eq (f : β → C) {X : C} {g h : X ⟶ pi f} (e : g = h) (b : β) : g ≫ pi.π f b = h ≫ pi.π f b := by subst e

@[simp] def pi.fan_π (f : β → C) (b : β) : (pi.fan f).π b = @pi.π C _ _ _ f b := rfl

def pi.lift {f : β → C} {P : C} (p : Π b, P ⟶ f b) : P ⟶ pi f :=
is_product.lift _ ⟨ ⟨ P ⟩, p ⟩

@[simp,search] def pi.lift_π {f : β → C} {P : C} (p : Π b, P ⟶ f b) (b : β) : pi.lift p ≫ pi.π f b = p b :=
by erw is_product.fac

def pi.map {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) : (pi f) ⟶ (pi g) :=
pi.lift (λ b, pi.π f b ≫ k b) 

@[simp] def pi.map_π {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) (b : β) : pi.map k ≫ pi.π g b = pi.π f b ≫ k b :=
by erw is_product.fac

def pi.pre {α} (f : α → C) (h : β → α) : pi f ⟶ pi (f ∘ h) :=
pi.lift (λ g, pi.π f (h g))

@[simp] def pi.pre_π {α} (f : α → C) (h : β → α) (b : β) : pi.pre f h ≫ pi.π (f ∘ h) b = pi.π f (h b) := 
by erw is_product.fac

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_products.{u v} D]
include 𝒟 

def pi.post (f : β → C) (G : C ⥤ D) : G (pi f) ⟶ (pi (G.obj ∘ f)) :=
@is_product.lift _ _ _ _ (pi.fan (G.obj ∘ f)) _ { X := _, π := λ b, G.map (pi.π f b) }

@[simp] def pi.post_π (f : β → C) (G : C ⥤ D) (b : β) : pi.post f G ≫ pi.π _ b = G.map (pi.π f b) := 
by erw is_product.fac
end

@[extensionality] lemma pi.hom_ext (f : β → C) {X : C} (g h : X ⟶ pi f) (w : ∀ b, g ≫ pi.π f b = h ≫ pi.π f b) : g = h :=
begin
  rw is_product.uniq'' g,
  rw is_product.uniq'' h,
  congr,
  ext,
  exact w x,
end

@[simp] def pi.lift_map 
  {f : β → C} {g : β → C} {P : C} (p : Π b, P ⟶ f b) (k : Π b, f b ⟶ g b) :
  pi.lift p ≫ pi.map k = pi.lift (λ b, p b ≫ k b) :=
by obviously

@[simp] def pi.map_map {f1 : β → C} {f2 : β → C} {f3 : β → C} 
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  pi.map k1 ≫ pi.map k2 = pi.map (λ b, k1 b ≫ k2 b) := 
by obviously

-- TODO lemmas describing interactions:
-- lift_pre, map_pre, pre_pre, lift_post, map_post, pre_post, post_post

end

section
variables [has_coproducts.{u v} C] {β : Type v} 

def sigma.cofan (f : β → C) := has_coproducts.coprod.{u v} f
def sigma (f : β → C) : C := (sigma.cofan f).X
def sigma.ι (f : β → C) (b : β) : f b ⟶ sigma f := (sigma.cofan f).ι b
instance sigma.universal_property (f : β → C) : is_coproduct (sigma.cofan f) := has_coproducts.is_coproduct.{u v} C f

@[simp] def sigma.cofan_ι (f : β → C) (b : β) : (sigma.cofan f).ι b = @sigma.ι C _ _ _ f b := rfl

def sigma.desc {f : β → C} {P : C} (p : Π b, f b ⟶ P) : sigma f ⟶ P :=
is_coproduct.desc _ ⟨ ⟨ P ⟩, p ⟩

@[simp,search] def sigma.lift_ι {f : β → C} {P : C} (p : Π b, f b ⟶ P) (b : β) : sigma.ι f b ≫ sigma.desc p = p b :=
by erw is_coproduct.fac

def sigma.map {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) : (sigma f) ⟶ (sigma g) :=
sigma.desc (λ b, k b ≫ sigma.ι g b) 

@[simp] def sigma.map_ι {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) (b : β) : sigma.ι f b ≫ sigma.map k = k b ≫ sigma.ι g b :=
by erw is_coproduct.fac

def sigma.pre {α} (f : α → C) (h : β → α) : sigma (f ∘ h) ⟶ sigma f :=
sigma.desc (λ g, sigma.ι f (h g))

@[simp] def sigma.pre_ι {α} (f : α → C) (h : β → α) (b : β) : sigma.ι (f ∘ h) b ≫ sigma.pre f h = sigma.ι f (h b) := 
by erw is_coproduct.fac

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_coproducts.{u v} D]
include 𝒟 

def sigma.post (f : β → C) (G : C ⥤ D) : (sigma (G.obj ∘ f)) ⟶ G (sigma f) :=
@is_coproduct.desc _ _ _ _ (sigma.cofan (G.obj ∘ f)) _ { X := _, ι := λ b, G.map (sigma.ι f b) }

@[simp] def sigma.post_π (f : β → C) (G : C ⥤ D) (b : β) : sigma.ι _ b ≫ sigma.post f G = G.map (sigma.ι f b) := 
by erw is_coproduct.fac
end

@[extensionality] lemma sigma.hom_ext (f : β → C) {X : C} (g h : sigma f ⟶ X) (w : ∀ b, sigma.ι f b ≫ g = sigma.ι f b ≫ h) : g = h :=
begin
  rw is_coproduct.uniq'' g,
  rw is_coproduct.uniq'' h,
  congr,
  ext,
  exact w x,
end

@[simp] def sigma.desc_map 
  {f : β → C} {g : β → C} {P : C} (k : Π b, f b ⟶ g b) (p : Π b, g b ⟶ P) :
  sigma.map k ≫ sigma.desc p = sigma.desc (λ b, k b ≫ p b) :=
by obviously

@[simp] def sigma.map_map {f1 : β → C} {f2 : β → C} {f3 : β → C} 
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  sigma.map k1 ≫ sigma.map k2 = sigma.map (λ b, k1 b ≫ k2 b) := 
by obviously

-- TODO lemmas describing interactions:
-- desc_pre, map_pre, pre_pre, desc_post, map_post, pre_post, post_post

end

end category_theory.limits
