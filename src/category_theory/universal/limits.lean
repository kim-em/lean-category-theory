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

section terminal
structure is_terminal (t : C) :=
(lift : ∀ (s : C), s ⟶ t)
(uniq : ∀ (s : C) (m : s ⟶ t), m = lift s . obviously)

restate_axiom is_terminal.uniq
attribute [ematch, back'] is_terminal.uniq_lemma

@[extensionality] lemma is_terminal.ext {X : C} (P Q : is_terminal.{u v} X) : P = Q := 
begin cases P, cases Q, obviously, end

lemma homs_to_terminal_ext (X' : C) (X : C) (B : is_terminal.{u v} X) (f g : X' ⟶ X) : f = g :=
begin
  rw B.uniq X' f,
  rw B.uniq X' g,
end

end terminal

section binary_product
structure is_binary_product {Y Z : C} (t : span Y Z) :=
(lift : ∀ (s : span Y Z), s.X ⟶ t.X)
(fac₁ : ∀ (s : span Y Z), (lift s) ≫ t.π₁ = s.π₁ . obviously) 
(fac₂ : ∀ (s : span Y Z), (lift s) ≫ t.π₂ = s.π₂ . obviously) 
(uniq : ∀ (s : span Y Z) (m : s.X ⟶ t.X) (w₁ : m ≫ t.π₁ = s.π₁) (w₂ : m ≫ t.π₂ = s.π₂), m = lift s . obviously)

restate_axiom is_binary_product.fac₁
attribute [simp,ematch] is_binary_product.fac₁_lemma
restate_axiom is_binary_product.fac₂
attribute [simp,ematch] is_binary_product.fac₂_lemma
restate_axiom is_binary_product.uniq
attribute [ematch, back'] is_binary_product.uniq_lemma

@[extensionality] lemma is_binary_product.ext {Y Z : C} {t : span Y Z} (P Q : is_binary_product t) : P = Q :=
begin cases P, cases Q, obviously end

instance {Y Z : C} {t : span Y Z} : subsingleton (is_binary_product t) := 
begin 
  fsplit, intros,
  apply is_binary_product.ext, -- obviously will do this after https://github.com/leanprover/mathlib/pull/269
end

lemma is_binary_product.uniq' {Y Z : C} {t : span Y Z} (h : is_binary_product t) {X' : C} (m : X' ⟶ t.X) : 
  m = h.lift { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } :=
h.uniq { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } m (by obviously) (by obviously)

-- TODO provide alternative constructor using uniq' instead of uniq.

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

lemma homs_to_binary_product_ext {Y Z : C} (t : span.{u v} Y Z) (B : is_binary_product t) {X : C} 
  {f g : X ⟶ t.X} (w₁ : f ≫ t.π₁ = g ≫ t.π₁) (w₂ : f ≫ t.π₂ = g ≫ t.π₂) : f = g :=
begin
  rw B.uniq' f,
  rw B.uniq' g,
  congr ; assumption
end

end binary_product

section product
variables {β : Type v} {f : β → C} 

structure is_product (t : fan f) :=
(lift : ∀ (s : fan f), s.X ⟶ t.X)
(fac  : ∀ (s : fan f), ∀ b, (lift s) ≫ t.π b = s.π b . obviously) 
(uniq : ∀ (s : fan f) (m : s.X ⟶ t.X) (w : ∀ b, m ≫ t.π b = s.π b), m = lift s . obviously)

restate_axiom is_product.fac
attribute [simp,ematch] is_product.fac_lemma
restate_axiom is_product.uniq
attribute [ematch, back'] is_product.uniq_lemma

@[extensionality] lemma is_product.ext {t : fan f} (P Q : is_product t) : P = Q :=
begin cases P, cases Q, obviously end

instance is_product_subsingleton {t : fan f}  : subsingleton (is_product t) := 
begin 
  fsplit, intros,
  apply is_product.ext, -- obviously will do this after https://github.com/leanprover/mathlib/pull/269
end

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

@[extensionality] lemma homs_to_product_ext {t : fan f} (B : is_product.{u v} t) {X : C} (f g : X ⟶ t.X) (w : ∀ b, f ≫ t.π b = g ≫ t.π b) : f = g :=
begin
  rw B.uniq' f,
  rw B.uniq' g,
  congr,
  ext,
  exact w x,
end

end product

section equalizer
variables {Y Z : C}
structure is_equalizer {f g : Y ⟶ Z} (t : fork f g) :=
(lift : ∀ (s : fork f g), s.X ⟶ t.X)
(fac  : ∀ (s : fork f g), (lift s) ≫ t.ι = s.ι . obviously)
(uniq : ∀ (s : fork f g) (m : s.X ⟶ t.X) (w : m ≫ t.ι = s.ι), m = lift s . obviously)

restate_axiom is_equalizer.fac
attribute [simp,ematch] is_equalizer.fac_lemma
restate_axiom is_equalizer.uniq
attribute [ematch, back'] is_equalizer.uniq_lemma

@[extensionality] lemma is_equalizer.ext {f g : Y ⟶ Z} {t : fork f g} (P Q : is_equalizer t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_equalizer.mono {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) : mono (t.ι) :=
{ right_cancellation := λ X' k l w, begin 
                                    let s : fork f g := { X := X', ι := k ≫ t.ι }, 
                                    have uniq_k := h.uniq s k (by obviously),
                                    have uniq_l := h.uniq s l (by obviously),
                                    obviously,
                              end }

lemma is_equalizer.univ {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) (s : fork f g) (φ : s.X ⟶ t.X) : (φ ≫ t.ι = s.ι) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_equalizer.of_lift_univ {f g : Y ⟶ Z} {t : fork f g}
  (lift : Π (s : fork f g), s.X ⟶ t.X)
  (univ : Π (s : fork f g) (φ : s.X ⟶ t.X), (φ ≫ t.ι = s.ι) ↔ (φ = lift s)) : is_equalizer t :=
{ lift := lift,
  fac := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))),
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

lemma homs_to_equalizer_ext {Y Z : C} {f g : Y ⟶ Z} (t : fork f g) (B : is_equalizer.{u v} t) {X : C} (h k : X ⟶ t.X) (w : h ≫ t.ι = k ≫ t.ι) : h = k :=
begin
  let s : fork f g := ⟨ ⟨ X ⟩, h ≫ t.ι ⟩,
  have q := B.uniq s h,
  have p := B.uniq s k,
  rw [q, ←p],
  solve_by_elim, refl
end

end equalizer

section pullback
variables {Y₁ Y₂ Z : C} {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} 
structure is_pullback (t : square r₁ r₂) :=
(lift : ∀ (s : square r₁ r₂), s.X ⟶ t.X)
(fac₁ : ∀ (s : square r₁ r₂), (lift s ≫ t.π₁) = s.π₁ . obviously)
(fac₂ : ∀ (s : square r₁ r₂), (lift s ≫ t.π₂) = s.π₂ . obviously)
(uniq : ∀ (s : square r₁ r₂) (m : s.X ⟶ t.X) (w₁ : (m ≫ t.π₁) = s.π₁) (w₂ : (m ≫ t.π₂) = s.π₂), m = lift s . obviously)

restate_axiom is_pullback.fac₁
attribute [simp,ematch] is_pullback.fac₁_lemma
restate_axiom is_pullback.fac₂
attribute [simp,ematch] is_pullback.fac₂_lemma
restate_axiom is_pullback.uniq
attribute [ematch, back'] is_pullback.uniq_lemma

@[extensionality] lemma is_pullback.ext {t : square r₁ r₂} (P Q : is_pullback t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_pullback.univ {t : square r₁ r₂} (h : is_pullback t) (s : square r₁ r₂) (φ : s.X ⟶ t.X) : 
  (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_pullback.of_lift_univ {t : square r₁ r₂}
  (lift : Π (s : square r₁ r₂), s.X ⟶ t.X)
  (univ : Π (s : square r₁ r₂) (φ : s.X ⟶ t.X), (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = lift s)) : 
  is_pullback t :=
{ lift := lift,
  fac₁ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).left,
  fac₂ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).right,
  uniq := begin obviously, apply univ_s_m.mp, obviously, end }

lemma homs_to_pullback_ext (t : square r₁ r₂) (B : is_pullback.{u v} t) 
  {X : C} (f g : X ⟶ t.X) (w₁ : f ≫ t.π₁ = g ≫ t.π₁) (w₂ : f ≫ t.π₂ = g ≫ t.π₂) : f = g :=
begin
  let s : square r₁ r₂ := ⟨ ⟨ X ⟩, f ≫ t.π₁, f ≫ t.π₂ ⟩,
  have q := B.uniq s f,
  have p := B.uniq s g,
  rw [q, ←p],
  obviously,
end

end pullback

variable (C)

class has_terminal_object :=
(terminal    : C)
(is_terminal : is_terminal.{u v} terminal . obviously)

class has_binary_products :=
(prod    : Π (Y Z : C), span Y Z)
(is_binary_product : Π (Y Z : C), is_binary_product (prod Y Z) . obviously)

class has_products :=
(prod : Π {β : Type v} (f : β → C), fan.{u v} f)
(is_product : Π {β : Type v} (f : β → C), is_product (prod f) . obviously)

class has_equalizers :=
(equalizer : Π {Y Z : C} (f g : Y ⟶ Z), fork f g)
(is_equalizer : Π {Y Z : C} (f g : Y ⟶ Z), is_equalizer (equalizer f g) . obviously)

class has_pullbacks :=
(pullback : Π {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z), square r₁ r₂)
(is_pullback : Π {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z), is_pullback (pullback r₁ r₂) . obviously)

def terminal_object [has_terminal_object.{u v} C] : C := has_terminal_object.terminal.{u v} C

variable {C}

def terminal_object.universal_property [has_terminal_object.{u v} C] : is_terminal.{u v} (terminal_object.{u v} C) := 
has_terminal_object.is_terminal.{u v} C
def terminal_object.hom [has_terminal_object.{u v} C] (X : C) : (X ⟶ terminal_object.{u v} C) := 
terminal_object.universal_property.lift.{u v} X

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

@[simp,ematch] lemma prod.pair_π₁ {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : prod.pair f g ≫ prod.π₁ Q R = f := 
(prod.universal_property.{u v} Q R).fac₁_lemma { X := P, π₁ := f, π₂ := g }
@[simp,ematch] lemma prod.pair_π₂ {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : prod.pair f g ≫ prod.π₂ Q R = g :=
(prod.universal_property.{u v} Q R).fac₂_lemma { X := P, π₁ := f, π₂ := g }

-- TODO remove duplication; this is done above, isn't it?
@[extensionality] def prod.characterisation (Y Z : C) (X : C) 
  (f g : X ⟶ prod Y Z) 
  (w₁ : f ≫ prod.π₁ Y Z = g ≫ prod.π₁ Y Z) 
  (w₂ : f ≫ prod.π₂ Y Z = g ≫ prod.π₂ Y Z) : f = g := 
begin 
  apply homs_to_binary_product_ext, obviously,
end
end

section
variables [has_products.{u v} C] {β : Type v} 

def pi.fan (f : β → C) := has_products.prod.{u v} f
def pi (f : β → C) : C := (pi.fan f).X
def pi.π (f : β → C) (b : β) : pi f ⟶ f b := (pi.fan f).π b
@[back] def pi.universal_property (f : β → C) : is_product (pi.fan f) := has_products.is_product.{u v} C f
def pi.lift (f : β → C) (g : fan f) := (pi.universal_property f).lift g

@[simp] def pi.fan_π (f : β → C) (b : β) : (pi.fan f).π b = @pi.π C _ _ _ f b := rfl
@[simp] def pi.lift_π (f : β → C) (g : fan f) (b : β) : (pi.universal_property f).lift g ≫ pi.π f b = g.π b :=
(pi.universal_property f).fac g b

def pi.of_components {f : β → C} {P : C} (p : Π b, P ⟶ f b) : P ⟶ pi f :=
(pi.universal_property f).lift ⟨ ⟨ P ⟩, p ⟩

@[simp] def pi.of_components_π {f : β → C} {P : C} (p : Π b, P ⟶ f b) (b : β) : pi.of_components p ≫ pi.π f b = p b :=
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

section
variables [has_equalizers.{u v} C] {Y Z : C} (f g : Y ⟶ Z)

def equalizer.fork := has_equalizers.equalizer.{u v} f g
def equalizer := (equalizer.fork f g).X
def equalizer.ι : (equalizer f g) ⟶ Y := (equalizer.fork f g).ι

def equalizer.lift (P : C) (h : P ⟶ Y) (w : h ≫ f = h ≫ g) : P ⟶ equalizer f g := 
(has_equalizers.is_equalizer.{u v} C f g ).lift { X := P, ι := h, w := w }

end

section
variables [has_pullbacks.{u v} C] {Y₁ Y₂ Z : C}

def pullback.square (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z) := has_pullbacks.pullback.{u v} r₁ r₂
def pullback (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z) := (pullback.square r₁ r₂).X
def pullback.π₁ (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z) : pullback r₁ r₂ ⟶ Y₁ := (pullback.square r₁ r₂).π₁
def pullback.π₂ (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z) : pullback r₁ r₂ ⟶ Y₂ := (pullback.square r₁ r₂).π₂
end

end

end category_theory.universal

