-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

namespace categories

universes u v

class category (Obj : Type (u+1)) : Type (u+1) :=
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

notation `𝟙` := category.identity   -- type as \b1
infixr ` ≫ `:80 := category.compose -- type as \gg
infixr ` ⟶ `:10  := category.Hom             -- type as \h

-- We now provide lemmas for the fields of category, without the auto_param junk
make_lemma category.left_identity
make_lemma category.right_identity
make_lemma category.associativity
attribute [simp] category.left_identity_lemma category.right_identity_lemma category.associativity_lemma 
attribute [ematch] category.associativity_lemma 
-- @[simp] def category.left_identity_lemma (f : X ⟶ Y) : 𝟙 X ≫ f = f := by rw category.left_identity
-- @[simp] def category.right_identity_lemma (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by rw category.right_identity
-- @[simp,ematch] def category.associativity_lemma (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : (f ≫ g) ≫ h = f ≫ (g ≫ h) := by rw category.associativity

instance category.has_one : has_one (X ⟶ X) := {
  one := 𝟙 X
}

@[simp] def category.left_identity_lemma' (f : X ⟶ Y) : 1 ≫ f = f := begin unfold has_one.one, simp end
@[simp] def category.right_identity_lemma' (f : X ⟶ Y) : f ≫ 1 = f := begin unfold has_one.one, simp end

-- TODO are these used?
@[simp,ematch] lemma category.identity_idempotent (X : C) : 𝟙 X ≫ 𝟙 X = 𝟙 X := by simp
@[simp,ematch] lemma category.identity_idempotent' (X : C) : (1 : X ⟶ X) ≫ (1 : X ⟶ X) = (1 : X ⟶ X) := begin unfold has_one.one, simp end

end categories
