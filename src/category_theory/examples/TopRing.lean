import .rings
import analysis.topology.topological_structures

universes u

open category_theory

namespace category_theory.examples

structure TopRing :=
{α : Type u}
[is_comm_ring : comm_ring α]
[is_topological_space : topological_space α]
[is_topological_ring : topological_ring α]

instance : has_coe_to_sort TopRing :=
{ S := Type u, coe := TopRing.α }

instance TopRing_comm_ring (R : TopRing) : comm_ring R := R.is_comm_ring
instance TopRing_topological_space (R : TopRing) : topological_space R := R.is_topological_space
instance TopRing_topological_ring (R : TopRing) : topological_ring R := R.is_topological_ring

instance TopRing_category : category TopRing :=
{ hom   := λ R S, {f : R → S // is_ring_hom f ∧ continuous f },
  id    := λ R, ⟨id, by obviously⟩,
  comp  := λ R S T f g, ⟨g.val ∘ f.val,
    begin -- TODO automate
      cases f, cases g, cases f_property, cases g_property, split,
      dsimp, resetI, apply_instance,
      dsimp, apply continuous.comp ; assumption
    end⟩ }.

namespace TopRing
/-- The forgetful functor to CommRing. -/
def forget_to_CommRing : TopRing ⥤ CommRing :=
{ obj := λ R, { α := R, str := examples.TopRing_comm_ring R },
  map' := λ R S f, ⟨ f.1, f.2.left ⟩ }

instance : faithful (forget_to_CommRing) := by tidy
end TopRing

end category_theory.examples
