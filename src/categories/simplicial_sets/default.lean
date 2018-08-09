import category_theory.category
import categories.tactics.obviously

open category_theory

def simplicial_operator (n m : ℕ) := { f : fin n → fin m // ∀ i < n - 1, f ⟨ i, sorry ⟩ ≤ f ⟨ i + 1, sorry ⟩ }

def Δ : category ℕ := 
{ Hom  := λ n m, simplicial_operator n m,
  comp := λ _ _ _ f g, ⟨ g.1 ∘ f.1, sorry ⟩, 
  id   := λ n, ⟨ id, sorry ⟩, }

-- def SimplicialSet := Presheaf Δ 