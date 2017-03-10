-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

/-
-- We've decided that Obj and Hom should be fields of Category, rather than parameters.
-- Mostly this is for the sake of simpler signatures, but it's possible that it is not the right choice.
-- Functor and NaturalTransformation are each parameterized by both their source and target.
-/

namespace tqft.categories

universe variables u v

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v) 
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f)
  (right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity Y) = f)
  (associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

attribute [ematch,simp] Category.left_identity
attribute [ematch,simp] Category.right_identity
attribute [ematch] Category.associativity

instance Category_to_Hom : has_coe_to_fun Category :=
{ F   := λ C, C^.Obj → C^.Obj → Type v,
  coe := Category.Hom }

@[ematch] definition Category.identity_idempotent
  ( C : Category )
  ( X : C^.Obj ) : C^.identity X = C^.compose (C^.identity X) (C^.identity X) := ♮
  
end tqft.categories
