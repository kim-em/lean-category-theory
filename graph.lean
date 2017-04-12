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

notation a :: b := path.cons a b
notation `p[` l:(foldr `, ` (h t, path.cons h t) path.nil _ `]`) := l

inductive {u v} path_of_paths { G : Graph.{u v} } : vertices G → vertices G → Type (max u v)
| nil  : Π ( h : G.vertices ), path_of_paths h h
| cons : Π { h s t : G.vertices } ( e : path h s ) ( l : path_of_paths s t ), path_of_paths h t

notation a :: b := path_of_paths.cons a b
notation `pp[` l:(foldr `, ` (h t, path_of_paths.cons h t) path_of_paths.nil _ `]`) := l

-- The pattern matching trick used here was explained by Jeremy Avigad at https://groups.google.com/d/msg/lean-user/JqaI12tdk3g/F9MZDxkFDAAJ
definition concatenate_paths
 { G : Graph } :
 Π { x y z : G.vertices }, path x y → path y z → path x z
| ._ ._ _ (path.nil _)               q := q
| ._ ._ _ (@path.cons ._ _ _ _ e p') q := path.cons e (concatenate_paths p' q)

definition concatenate_path_of_paths
 { G : Graph } :
 Π { x y : G.vertices }, path_of_paths x y → path x y
| ._ ._ (path_of_paths.nil X) := path.nil X
| ._ ._ (@path_of_paths.cons ._ _ _ _ e p') := concatenate_paths e (concatenate_path_of_paths p')

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
