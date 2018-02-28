-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

namespace categories

universes u v

class category (Obj : Type (u+1)) :=
  (Hom : Obj → Obj → Type u)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f . obviously)
  (right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f . obviously)
  (associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h) . obviously)

variable {C : Type (u+1)}
variables {W X Y Z : C}
variable [category C]

-- def Hom : C → C → Type u := category.Hom
-- def identity : Π X : C, Hom X X := category.identity
-- def compose : Π {X Y Z : C}, Hom X Y → Hom Y Z → Hom X Z := @category.compose C _

notation `𝟙` := category.identity   -- type as \b1
infixr ` ≫ `:80 := category.compose -- type as \gg
infixr ` ⟶ `:10  := category.Hom             -- type as \h

set_option pp.all true
-- We now provide lemmas for the fields of category, that use `Hom`.
@[simp] def category.left_identity_lemma (f : X ⟶ Y) : 𝟙 X ≫ f = f := by rw category.left_identity
@[simp] def category.right_identity_lemma (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by rw category.right_identity
@[simp,ematch] def category.associativity_lemma (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : (f ≫ g) ≫ h = f ≫ (g ≫ h) := by rw category.associativity

-- 
instance category.has_one : has_one (X ⟶ X) := {
  one := 𝟙 X
}

@[simp] def category.left_identity_lemma' (f : X ⟶ Y) : 1 ≫ f = f := begin unfold has_one.one, simp end
@[simp] def category.right_identity_lemma' (f : X ⟶ Y) : f ≫ 1 = f := begin unfold has_one.one, simp end

@[simp,ematch] lemma category.identity_idempotent (X : C) : 𝟙 X ≫ 𝟙 X = 𝟙 X := by simp
@[simp,ematch] lemma category.identity_idempotent' (X : C) : (1 : X ⟶ X) ≫ (1 : X ⟶ X) = (1 : X ⟶ X) := begin unfold has_one.one, simp end

@[simp] def category.cancel_left (f g : X ⟶ Y) : (∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) ↔ f = g :=
begin
split,
{ intro w, its w (𝟙 Y), tidy },
{ obviously }
end
@[simp] def category.cancel_right (f g : Y ⟶ Z) : (∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) ↔ f = g :=
begin
split,
{ intro w, its w (𝟙 Y), tidy },
{ obviously }
end
@[simp] def category.identity.if_it_quacks_left (f : X ⟶ X) : (∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) ↔ f = 𝟙 X :=
begin
split,
{ intro w, its w (𝟙 X), tidy },
{ obviously }
end
@[simp] def category.identity.if_it_quacks_right (f : X ⟶ X) : (∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) ↔ f = 𝟙 X :=
begin
split,
{ intro w, its w (𝟙 X), tidy },
{ obviously }
end

end categories
