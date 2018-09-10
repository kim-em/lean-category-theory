import category_theory.opposites

namespace category_theory

universes u₁ v₁

-- def OppositeOpposite (C : Category) : equivalence (Opposite (Opposite C)) C := sorry
-- PROJECT opposites preserve products, functors, slices.

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

@[simp] lemma opop : @category_theory.opposite (Cᵒᵖ) (@category_theory.opposite C 𝒞) = 𝒞 := 
begin
  tactic.unfreeze_local_instances,
  cases 𝒞,
  unfold category_theory.opposite,
  congr,
end

end category_theory