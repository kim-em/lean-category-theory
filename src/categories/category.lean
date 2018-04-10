-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

namespace categories

universe u

/-
-- The universe annotations may be suprising here!
-- Note that we ask the Obj : Type (u+1), while Hom X Y : Type u.
-- This is motivated by:
-- 1. As `category` is a class, we want all universe levels to be determined by its parameters.
--    (Thus we want to avoid independent universe levels for Obj and Hom.)
-- 2. The basic example of category is the category of types and functions.
--    This example matches the definition here.
-- 3. It so far doesn't seem to cause any problems!
-/

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
attribute [simp,search] category.left_identity_lemma category.right_identity_lemma category.associativity_lemma 
attribute [search] category.associativity_lemma 

instance category.has_one : has_one (X ⟶ X) := {
  one := 𝟙 X
}

@[simp] def category.left_identity_lemma' (f : X ⟶ Y) : 1 ≫ f = f := begin unfold has_one.one, simp end
@[simp] def category.right_identity_lemma' (f : X ⟶ Y) : f ≫ 1 = f := begin unfold has_one.one, simp end

end categories
