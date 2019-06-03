-- import category_theory.presheaves.sheaves
-- import topology.Top.stalks
-- import algebra.CommRing.limits
-- import ring_theory.ideals

-- universes v

-- open category_theory.examples
-- open category_theory.presheaves
-- open category_theory.limits

-- variables (X : Top.{v})

-- instance : has_colimits.{v+1 v} CommRing := sorry

-- def structure_sheaf := sheaf.{v+1 v} X CommRing

-- structure ringed_space :=
-- (𝒪 : structure_sheaf X)

-- structure locally_ringed_space extends ringed_space X :=
-- (locality : ∀ x : X, is_local_ring (stalk_at.{v+1 v} 𝒪.presheaf x).1) -- coercion from sheaf to presheaf?

-- def ringed_space.of_topological_space : ringed_space X :=
-- { 𝒪 := { presheaf := { obj       := λ U, sorry /- ring of continuous functions U → ℂ -/,
--                         map       := sorry,
--                         map_id'   := sorry,
--                         map_comp' := sorry },
--           sheaf_condition := sorry,
--   } }