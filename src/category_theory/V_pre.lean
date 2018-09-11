import category_theory.sheaves
import analysis.topology.topological_structures

universes u v

open category_theory
open category_theory.examples

structure TopRing :=
{β : Type u}
[Ring : comm_ring β]
[Top : topological_space β]
[TopRing : topological_ring β]

instance TopRing_comm_ring (R : TopRing) : comm_ring R.β := R.Ring
instance TopRing_topological_space (R : TopRing) : topological_space R.β := R.Top
instance TopRing_topological_ring (R : TopRing) : topological_ring R.β := R.TopRing

instance : category TopRing :=
{ hom   := λ R S, {f : R.β → S.β // is_ring_hom f ∧ continuous f },
  id    := λ R, ⟨id, sorry⟩,
  comp  := λ R S T f g, ⟨g.val ∘ f.val, sorry⟩ }

variables (α : Type v) [topological_space α]

structure presheaf_TopRing :=
(𝒪 : presheaf (open_set α) TopRing)

structure Presheaf_TopRing :=
{α : Type v}
[Top_α : topological_space α]
(presheaf : presheaf_TopRing α)

instance Presheaf_TopRing_topological_space (F : Presheaf_TopRing) : topological_space F.α := F.Top_α 

structure Presheaf_TopRing_hom (F G : Presheaf_TopRing) :=
(f : F.α → G.α)
[continuity : continuous f]
(c : F.presheaf.𝒪 ⟹ (sorry : ((open_set F.α)ᵒᵖ) ⥤ ((open_set G.α)ᵒᵖ)) ⋙ G.presheaf.𝒪)

-- instance category Presheaf_TopRing :=
-- { hom := λ F G, 

-- }