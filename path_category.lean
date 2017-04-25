-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import .functor
import .graph
import .examples.types.types

open tqft.categories

namespace tqft.categories.graph

definition PathCategory ( G : Graph ) : Category :=
{
  Obj            := G.vertices,
  Hom            := λ x y, path x y,
  identity       := λ x, path.nil x,
  compose        := λ _ _ _ f g, concatenate_paths f g,
  left_identity  := ♮,
  right_identity := begin
                      blast,
                      induction f,
                      -- when f is nil
                      dsimp,
                      trivial,
                      -- when f is cons
                      dsimp,
                      exact congr_arg (λ p, path.cons e p) ih_1
                    end,
  associativity  := begin
                      blast,
                      induction f,
                      -- when f is nil
                      dsimp,
                      trivial,
                      -- when f is cons
                      dsimp,
                      exact congr_arg (λ p, path.cons e p) (ih_1 g)
                    end
}

structure GraphHomomorphism ( G H : Graph ) := 
  ( onVertices : G.vertices → H.vertices )
  ( onEdges    : ∀ { X Y : G.vertices }, G.edges X Y → H.edges (onVertices X) (onVertices Y) )

definition Graph.from_Category ( C : Category ) : Graph := {
    vertices := C.Obj,
    edges    := λ X Y, C.Hom X Y
  }

instance Category_to_Graph_coercion: has_coe Category Graph :=
  { coe := Graph.from_Category }

open tqft.categories.functor

definition path_to_morphism
  { G : Graph }
  { C : Category }
  ( H : GraphHomomorphism G C )
  : Π { X Y : G.vertices }, path X Y → C.Hom (H.onVertices X) (H.onVertices Y) 
| ._ ._ (path.nil Z)              := C.identity (H.onVertices Z)
| ._ ._ (@path.cons ._ _ _ _ e p) := C.compose (H.onEdges e) (path_to_morphism p)

-- PROJECT obtain this as the left adjoint to the forgetful functor.
-- set_option pp.implicit true
definition Functor.from_GraphHomomorphism { G : Graph } { C : Category } ( H : GraphHomomorphism G C ) : Functor (PathCategory G) C :=
{
  onObjects     := H.onVertices,
  onMorphisms   := λ _ _ f, path_to_morphism H f,
  identities    := ♮,
  functoriality := begin
                     blast,
                     unfold PathCategory,
                     dsimp,
                     induction f,
                     blast,
                     dsimp,
                     pose p := ih_1 g,
                     unfold concatenate_paths,
                     unfold path_to_morphism,
                     rewrite p,
                     dsimp,                       -- FIXME, this and the next line are required because of https://github.com/leanprover/lean/issues/1509
                     unfold Graph.from_Category,
                     rewrite - C.associativity,
                   end
}

instance GraphHomomorphism_to_Functor_coercion { G : Graph } { C : Category }: has_coe (GraphHomomorphism G C) (Functor (PathCategory G) C) :=
  { coe := Functor.from_GraphHomomorphism }

end tqft.categories.graph
