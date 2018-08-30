import category_theory.sheaves
import category_theory.examples.rings.universal

universes v

open category_theory.examples
open category_theory.universal

variables {α : Type v}

structure structure_sheaf (X : topological_space α) extends 𝒪 : sheaf.{v+1 v} X Ring :=
(locality : ∀ x : α, local_ring (stalk_at.{v+1 v} 𝒪 x).1)

structure locally_ringed_space :=
(X : topological_space α)
(𝒪 : structure_sheaf X)

def locally_ringed_space.of_topological_space (X : topological_space α) : locally_ringed_space :=
{ X := X,
  𝒪 := { presheaf := { obj       := λ U, sorry /- ring of continuous functions U → ℂ -/,
                        map'      := sorry,
                        map_id'   := sorry,
                        map_comp' := sorry },
          sheaf_condition := sorry,
          locality := sorry
  } }