-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.isomorphism

open categories
open categories.isomorphism

universes u v

variable {C : Type u}
variable [C_cat : uv_category.{u v} C]
include C_cat

def End (X : C) := X ⟶ X
def Aut (X : C) := X ≅ X

instance {X : C} : monoid (End X) :=
begin
  refine {
    one := 𝟙 X,
    mul := λ x y, x ≫ y,
    ..
  },
  obviously,
end

instance {X : C} : group (Aut X) :=
begin
  refine {
     one := Isomorphism.refl X,
     inv := Isomorphism.symm,
     mul := Isomorphism.trans,
     ..
  },
  obviously,
end