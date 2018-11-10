import category_theory.path_category
import tactic.linarith

open category_theory.graphs

universes u₁ v₁

namespace category_theory

def finite_graph {n k : ℕ} (e : vector (fin n × fin n) k) := ulift.{v₁} (fin n)

instance finite_graph_category {n k : ℕ} (e : vector (fin n × fin n) k) : graph.{v₁ v₁} (finite_graph e) :=
{ edges := λ x y, ulift { a : fin k // e.nth a = (x.down, y.down) } }

def parallel_pair : vector (fin 2 × fin 2) 2 := ⟨ [(0, 1), (0, 1)], by refl ⟩

-- Verify typeclass inference is hooked up correctly:
example : category.{v₁ v₁} (paths (finite_graph parallel_pair)) := by apply_instance.

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

@[simp] def graph_functor {n k : ℕ} {e : vector (fin n × fin n) k}
  (objs : vector C n) (homs : Π m : fin k, objs.nth (e.nth m).1 ⟶ objs.nth (e.nth m).2) :
  paths (finite_graph.{v₁} e) ⥤ C :=
functor.of_graph_hom
{ onVertices := λ x, objs.nth x.down,
  onEdges := λ x y f,
  begin
    have p := homs f.down.val,
    refine (eq_to_hom _) ≫ p ≫ (eq_to_hom _), -- TODO this needs a name, e.g. `convert_hom`
    rw f.down.property,
    rw f.down.property,
  end}


def parallel_pair_functor' {X Y : C} (f g : X ⟶ Y) : paths.{v₁} (finite_graph parallel_pair) ⥤ C :=
graph_functor ⟨ [X, Y], by refl ⟩
(λ m, match m with
| ⟨ 0, _ ⟩ := f
| ⟨ 1, _ ⟩ := g
| ⟨ n+2, _ ⟩ := by exfalso; linarith
end)

end category_theory
