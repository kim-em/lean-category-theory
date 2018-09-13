-- import category_theory.sheaves
-- import category_theory.examples.rings.universal

-- universes v

-- open category_theory.examples
-- open category_theory.limits

-- variables (α : Type v) [topological_space α]

-- def structure_sheaf := sheaf.{v+1 v} α CommRing

-- structure ringed_space :=
-- (𝒪 : structure_sheaf α)
 
-- structure locally_ringed_space extends ringed_space α :=
-- (locality : ∀ x : α, local_ring (stalk_at.{v+1 v} 𝒪 x).1)

-- def ringed_space.of_topological_space : ringed_space α :=
-- { 𝒪 := { presheaf := { obj       := λ U, sorry /- ring of continuous functions U → ℂ -/,
--                         map'      := sorry,
--                         map_id'   := sorry,
--                         map_comp' := sorry },
--           sheaf_condition := sorry,
--   } }