import category_theory.types

namespace category_theory

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

-- This is just the comma category *↓F. Does it deserve a separate identity?

def grothendieck_category (F : C ⥤ Type u) : category (Σ c : C, F.obj c) :=
{ hom := λ p q, { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 },
  id := λ p, ⟨ 𝟙 p.1, by obviously ⟩,
  comp := λ p q r f g, ⟨ f.val ≫ g.val, by obviously ⟩ }

end category_theory