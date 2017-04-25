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

end tqft.categories.graph
