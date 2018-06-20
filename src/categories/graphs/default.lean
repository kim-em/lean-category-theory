-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import categories.tactics
import tidy.auto_cast

namespace categories.graphs

universes u₁ u₂

class graph (vertices : Type u₁) :=
  (edges : vertices → vertices → Type u₁)

variable {C : Type u₁}
variables {W X Y Z : C}
variable [graph C]

def edges : C → C → Type u₁ := graph.edges

structure graph_homomorphism (G : Type u₁) [graph G] (H : Type u₂) [graph H] := 
  (onVertices : G → H)
  (onEdges    : ∀ {X Y : G}, edges X Y → edges (onVertices X) (onVertices Y))

variable {G : Type u₁}
variable [graph G]
variable {H : Type u₂}
variable [graph H]

@[extensionality] lemma graph_homomorphisms_pointwise_equal
  {p q : graph_homomorphism G H} 
  (vertexWitness : ∀ X : G, p.onVertices X = q.onVertices X) 
  (edgeWitness : ∀ X Y : G, ∀ f : edges X Y, ⟬ p.onEdges f ⟭ = q.onEdges f) : p = q :=
begin
  induction p with p_onVertices p_onEdges,
  induction q with q_onVertices q_onEdges,
  have h_vertices : p_onVertices = q_onVertices, exact funext vertexWitness,
  subst h_vertices,
  have h_edges : @p_onEdges = @q_onEdges, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  exact edgeWitness X Y f,
  subst h_edges
end

inductive path : G → G → Type u₁
| nil  : Π (h : G), path h h
| cons : Π {h s t : G} (e : edges h s) (l : path s t), path h t

notation a :: b := path.cons a b
notation `p[` l:(foldr `, ` (h t, path.cons h t) path.nil _ `]`) := l

inductive path_of_paths : G → G → Type (u₁+1)
| nil  : Π (h : G), path_of_paths h h
| cons : Π {h s t : G} (e : path h s) (l : path_of_paths s t), path_of_paths h t

notation a :: b := path_of_paths.cons a b
notation `pp[` l:(foldr `, ` (h t, path_of_paths.cons h t) path_of_paths.nil _ `]`) := l

-- The pattern matching trick used here was explained by Jeremy Avigad at https://groups.google.com/d/msg/lean-user/JqaI12tdk3g/F9MZDxkFDAAJ
definition concatenate_paths : Π {x y z : G}, path x y → path y z → path x z
| ._ ._ _ (path.nil _)               q := q
| ._ ._ _ (@path.cons ._ _ _ _ _ e p') q := path.cons e (concatenate_paths p' q)

@[simp] lemma concatenate_paths' {x' x y z : G} (e : edges x' x) (p : path x y) (q : path y z) : concatenate_paths (e :: p) q = e :: (concatenate_paths p q) := by refl

definition concatenate_path_of_paths : Π {x y : G}, path_of_paths x y → path x y
| ._ ._ (path_of_paths.nil X) := path.nil X
| ._ ._ (@path_of_paths.cons ._ _ _ _ _ e p') := concatenate_paths e (concatenate_path_of_paths p')

end categories.graphs
