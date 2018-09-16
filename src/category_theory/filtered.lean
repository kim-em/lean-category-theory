import category_theory.limits.shape
import order.filter

open category_theory.limits

namespace category_theory

universes u₁ v₁

variables α : Type u₁

class directed [preorder α] :=
(bound (x₁ x₂ : α) : α)
(i₁ (x₁ x₂ : α) : x₁ ≤ bound x₁ x₂)
(i₂ (x₁ x₂ : α) : x₂ ≤ bound x₁ x₂)

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞 

class filtered :=
(default : C)
(obj_bound (X Y : C) : cospan X Y)
(hom_bound {X Y : C} (f g : X ⟶ Y) : cofork f g)

instance [inhabited α] [preorder α] [directed α] : filtered.{u₁ u₁} α :=
{ default := default α,
  obj_bound := λ x y, { X := directed.bound x y, ι₁ := ⟨ ⟨ directed.i₁ x y ⟩ ⟩, ι₂ := ⟨ ⟨ directed.i₂ x y ⟩ ⟩ },
  hom_bound := λ _ y f g, { X := y, π := 𝟙 y, w' := begin cases f, cases f, cases g, cases g, simp end } }

end category_theory