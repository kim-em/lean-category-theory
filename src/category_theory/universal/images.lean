import category_theory.isomorphism

open category_theory

universes u v

namespace category_theory.universal

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables {X Y Z : C}

structure is_image (f : Y ⟶ Z) (ι : X ⟶ Z) :=
(mono : mono ι)
-- (fac  : sorry)

end category_theory.universal
