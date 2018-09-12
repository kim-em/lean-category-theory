import category_theory.category
import analysis.topology.topological_structures

universes u

open category_theory

namespace category_theory.examples

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
  id    := λ R, ⟨id, by obviously⟩,
  comp  := λ R S T f g, ⟨g.val ∘ f.val, 
    begin -- TODO automate
      cases f, cases g, cases f_property, cases g_property, split, 
      dsimp, resetI, apply_instance, 
      dsimp, apply continuous.comp ; assumption  
    end⟩ }

end category_theory.examples
