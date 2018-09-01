import category_theory.category
import category_theory.tactics.obviously

universes u₁

namespace category_theory

variables (α : Type u₁)

instance [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := by tidy,
  comp := begin tidy, transitivity Y; assumption end } -- automate, via mono?

end category_theory