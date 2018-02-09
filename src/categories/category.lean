-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics
import .graphs
import tidy.make_lemma

open categories.graphs

namespace categories

universes u v

class category (Obj : Type u) :=
  (Hom : Obj → Obj → Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f )
  (right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f )
  (associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h) )

-- because we provided default tactics for generating fields above, we need to extract separate lemmas as well.
make_lemma category.left_identity
make_lemma category.right_identity
make_lemma category.associativity
attribute [simp] category.left_identity_lemma category.right_identity_lemma
attribute [simp,ematch] category.associativity_lemma

def Hom {α : Type u} [category.{u v} α] : α → α → Type v := category.Hom

notation `𝟙` := category.identity
infixr ` >> `:80 := category.compose

@[ematch] lemma category.identity_idempotent {α} [category α] (X : α) :
  𝟙 X >> 𝟙 X = 𝟙 X := by simp

end categories
