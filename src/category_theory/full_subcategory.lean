-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

namespace categories

definition {u v w} Full_Subcategory ( C : Category.{u v} ) ( Z : C.Obj → Sort w ) : Category.{(max u w) v} :=
{
  Obj := Σ X : C.Obj, plift (Z X),
  Hom := λ X Y, C.Hom X.1 Y.1,
  identity       := by tidy, -- FIXME it would be nice if abstracts were reducible for the rest of the definition.
  compose        := λ _ _ _ f g, C.compose f g,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

end categories
