-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .functor

open categories.functor

namespace categories

local attribute [applicable] Category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition {u v w} FullSubcategory ( C : Category.{u v} ) ( Z : C.Obj → Sort w ) : Category.{(max u w) v} :=
{
  Obj := Σ X : C.Obj, plift (Z X),
  Hom := λ X Y, C.Hom X.1 Y.1,
  identity       := by tidy,
  compose        := λ _ _ _ f g, C.compose f g
}

definition {u1 v1 u2 v2 wc wd} Functor_restricts_to_FullSubcategory 
  { C : Category.{u1 v1} } 
  { D : Category.{u2 v2} } 
  ( F : Functor C D ) 
  ( ZC : C.Obj → Sort wc )
  ( ZD : D.Obj → Sort wd )
  ( w : ∀ { X : C.Obj } (z : ZC X), ZD (F.onObjects X) ) : Functor (FullSubcategory C ZC) (FullSubcategory D ZD) := {
    onObjects     := λ X, ⟨ F.onObjects X.1, ⟨ w X.2.down ⟩  ⟩,
    onMorphisms   := λ _ _ f, F.onMorphisms f
  }

end categories
