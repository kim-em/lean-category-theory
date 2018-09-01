import category_theory.category


namespace category_theory

universes u₁ v₁
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞 

class filtered :=
(empty : C)
(obj_bound (X Y : C) : Σ Z : C, (X ⟶ Z) × (Y ⟶ Z))
(hom_bound {X Y : C} (f g : X ⟶ Y) : Σ Z : C, { h : Y ⟶ Z // f ≫ h = g ≫ h })



end category_theory