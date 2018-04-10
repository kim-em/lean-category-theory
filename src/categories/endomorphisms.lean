-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .isomorphism

open categories
open categories.isomorphism

universe u

variable {C : Type (u+1)}
variable [category C]

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
     one := Isomorphism.id X,
     inv := Isomorphism.reverse,
     mul := Isomorphism.comp,
     ..
  },
  obviously,
end