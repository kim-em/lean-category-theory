-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category
import category_theory.graphs

open category_theory
open category_theory.graphs

namespace category_theory.examples.graphs

universe u₁

def Graph := Σ α : Type u₁, graph.{u₁} α

instance graph_from_Graph (G : Graph) : graph G.1 := G.2

structure Graph_hom (G H : Graph.{u₁}) : Type u₁ :=
(map : @graph_hom G.1 G.2 H.1 H.2)

@[extensionality] lemma graph_homomorphisms_pointwise_equal
  {G H : Graph.{u₁}}
  {p q : Graph_hom G H}
  (vertexWitness : ∀ X : G.1, p.map.onVertices X = q.map.onVertices X)
  (edgeWitness : ∀ X Y : G.1, ∀ f : edges X Y, ⟬ p.map.onEdges f ⟭ = q.map.onEdges f ) : p = q :=
begin
  induction p,
  induction q,
  tidy,
end

instance CategoryOfGraphs : large_category Graph :=
{ hom := Graph_hom,
  id := λ G,
  ⟨{ onVertices   := id,
     onEdges := λ _ _ f, f }⟩,
  comp := λ G H K f g,
  ⟨{ onVertices := λ v, g.map.onVertices (f.map.onVertices v),
     onEdges    := λ v w e, g.map.onEdges (f.map.onEdges e) }⟩ }

end category_theory.examples.graphs