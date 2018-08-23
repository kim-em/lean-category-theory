-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.isomorphism

namespace category_theory

universes u v

variable {C : Type u}
variable [𝒞 : category.{u v} C]
include 𝒞

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
     one := iso.refl X,
     inv := iso.symm,
     mul := iso.trans,
     ..
  },
  obviously,
end

end category_theory
