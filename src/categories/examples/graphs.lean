-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..category
import ..graphs

open categories
open categories.graphs

namespace categories.examples.graphs

universe u₁

definition Graph := Σ α : Type (u₁+1), graph α

instance graph_from_Graph (G : Graph) : graph G.1 := G.2

structure GraphHomomorphism (G H : Graph.{u₁}) : Type (u₁+1) := 
(map : @graph_homomorphism G.1 G.2 H.1 H.2)

@[applicable] lemma graph_homomorphisms_pointwise_equal
  {G H : Graph}
  {p q : GraphHomomorphism G H} 
  (vertexWitness : ∀ X : G.1, p.map.onVertices X = q.map.onVertices X) 
  (edgeWitness : ∀ X Y : G.1, ∀ f : edges X Y, ⟦ p.map.onEdges f ⟧ = q.map.onEdges f) : p = q :=
begin
  induction p,
  induction q,
  have h : p = q, begin tidy, exact (vertexWitness X), end, -- TODO automate
  subst h
end

instance CategoryOfGraphs : category Graph := {
  Hom := GraphHomomorphism,
  identity := λ G, ⟨ {
      onVertices   := id,
      onEdges := λ _ _ f, f
  } ⟩,
  compose := λ G H K f g, ⟨ {
      onVertices := λ v, g.map.onVertices (f.map.onVertices v),
      onEdges    := λ v w e, g.map.onEdges (f.map.onEdges e)
  } ⟩
}

end categories.examples.graphs