import category_theory.presheaves

open category_theory

universes u₁ v₁ u₂ v₂

namespace category_theory.presheaves

/- Presheaf to a 2-functor CAT ⥤₂ CAT, but we're not going to prove all of that yet. -/

namespace Presheaf

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C] (D : Type u₂) [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟
variable (F : C ⥤ D)

-- def map (F : C ⥤ D) : Presheaf.{u₁ v₁} C ⥤ Presheaf.{u₂ v₂} D := sorry

end Presheaf

end category_theory.presheaves