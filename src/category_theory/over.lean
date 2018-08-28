import category_theory.category
import category_theory.tactics.obviously

universes u₁ v₁

namespace category_theory

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

def over (Z : C) := Σ X : C, X ⟶ Z

instance {Z : C} : category (over Z) :=
{ hom := λ X Y, { f : X.1 ⟶ Y.1 // f ≫ Y.2 = X.2 },
  id := λ X, ⟨ 𝟙 X.1, by obviously ⟩,
  comp := λ X Y Z f g, ⟨ f.val ≫ g.val, by obviously ⟩ }.

end category_theory