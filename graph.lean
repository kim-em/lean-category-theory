-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import .functor
import .examples.types.types

open tqft.categories

namespace tqft.categories.graph

structure {u v} Graph :=
  ( vertices : Type u )
  ( edges : vertices → vertices → Type v )

open Graph

inductive {u v} path { G : Graph.{u v} } : vertices G → vertices G → Type (max u v)
| nil  : Π ( h : G.vertices ), path h h
| cons : Π { h s t : G.vertices } ( e : G.edges h s ) ( l : path s t ), path h t

@[unfoldable] definition concatenate_paths
 { G : Graph }
 { x y z : G.vertices } : path x y → path y z → path x z :=
     begin
       intros p q,
       induction p,
       -- Deal with the case with p is nil
       exact q,
       -- Now the case where p is a cons
       exact path.cons e (ih_1 q)
     end

@[unfoldable] definition PathCategory ( G : Graph ) : Category :=
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

-- TODO it would be nice if we could use:
-- definition path_to_morphism { G : Graph } { C : Category } ( h : GraphHomomorphism G C ) { X Y : G.vertices } : path X Y → C.Hom (h.onVertices X) (h.onVertices Y)
-- | (path.nil X)    := C.identity h.onVertices X
-- | (path.cons e p) := C.compose (h.onEdges e) (path_to_morphism p)

@[unfoldable] definition path_to_morphism { G : Graph } { C : Category } ( H : GraphHomomorphism G C ) { X Y : G.vertices } : path X Y → C.Hom (H.onVertices X) (H.onVertices Y) :=
begin
 intros p,
 induction p with Z h s t e p i,
 exact C.identity (H.onVertices Z),
 exact C.compose (H.onEdges e) i
end

definition Functor.from_GraphHomomorphism { G : Graph } { C : Category } ( H : GraphHomomorphism G C ) : Functor (PathCategory G) C :=
{
  onObjects     := H.onVertices,
  onMorphisms   := λ _ _ f, path_to_morphism H f,
  identities    := ♮,
  functoriality := begin
                     blast,
                     induction f,
                     simp,
                     pose p := ih_1 g,
                     blast
                   end
}

instance GraphHomomorphism_to_Functor_coercion { G : Graph } { C : Category }: has_coe (GraphHomomorphism G C) (Functor (PathCategory G) C) :=
  { coe := Functor.from_GraphHomomorphism }

end tqft.categories.graph
