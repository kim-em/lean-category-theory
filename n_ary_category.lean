-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

import .graph
import .category

open tqft.categories.graph

namespace tqft.categories.n_ary

definition {u v} compose_each_path
  { G : Graph.{u v} }
  { composition : Π { A B : G.vertices }, path A B → G.edges A B } :
   Π { X Y : G.vertices }, path_of_paths X Y → path X Y
| ._ ._ (path_of_paths.nil X) := path.nil X
| ._ ._ (@path_of_paths.cons ._ _ _ _ p ps) := path.cons (composition p) (compose_each_path ps)

structure {u v} n_ary_Category :=
  (graph : Graph.{u v})
  (identity : Π X : graph.vertices, graph.edges X X)
  (compose  : Π { X Y : graph.vertices }, path X Y → graph.edges X Y)
  (compose_empty_path  : ∀ ( X : graph.vertices ), compose ( p[] ) = identity X)
  (compose_length_one_path : ∀ { X Y : graph.vertices } ( f : graph.edges X Y ), compose ( p[f] ) = f )
  (associativity  : ∀ { X Y : graph.vertices } ( p : path_of_paths X Y ),
    compose (@compose_each_path graph @compose X Y p) = compose (concatenate_path_of_paths p))

attribute [simp,ematch] n_ary_Category.compose_empty_path
attribute [simp,ematch] n_ary_Category.compose_length_one_path
attribute [simp,ematch] n_ary_Category.associativity

open tqft.categories

definition {u v} compose_path
  { G : Graph.{u v} }
  { identity : Π X : G.vertices, G.edges X X }
  { composition : Π { A B C : G.vertices }, G.edges A B → G.edges B C → G.edges A C } :
   Π { X Y : G.vertices }, path X Y → G.edges X Y
| ._ ._ (path.nil X) := identity X
| ._ ._ (@path.cons ._ _ _ _ e p) := composition e (compose_path p)

definition {u v} n_ary_Category_to_Category ( C: n_ary_Category.{u v} ) : Category :=
{
  Obj := C.graph.vertices,
  Hom := C.graph.edges,
  identity := C.identity,
  compose := λ X Y Z f g, C.compose ( p[ f, g ] ),
  left_identity  := begin
                      intros,       
                      refine ( cast _ (C.associativity pp[ p[ ], p[ f ]]) ),
                      blast
                    end,
  right_identity := begin
                      intros,
                      refine ( cast _ (C.associativity pp[ p[ f ], p[ ]]) ),
                      blast                      
                    end,
  associativity  := begin
                      intros,

                      -- FIXME why don't these unfolds work?
                      -- pose p := (C.associativity pp[ p[ f, g ], p[ h ]]),
                      -- unfold n_ary.compose_each_path at p,
                      -- unfold graph.concatenate_path_of_paths at p,

                      -- pose q := (C.associativity pp[ p[ f ], p[ g, h ]]),
                      -- unfold n_ary.compose_each_path at q,
                      -- unfold graph.concatenate_path_of_paths at q,

                      admit
                    end
}

definition {u v} Category_to_n_ary_Category ( C : Category.{u v} ) : n_ary_Category :=
{
  graph := C,
  identity := λ X, C.identity X,
  compose  := λ X Y f, @compose_path C (C.identity) (@Category.compose C) X Y f,
  compose_empty_path := ♯,
  compose_length_one_path := ♯,
  associativity      := begin
                          blast,
                          induction p,
                          -- if p was nil
                          blast,
                          -- if p was a path
                          blast,
                          induction e with k l m n e p ih_2, -- FIXME if we leave off the last one here, we get two ih_1's
                          -- if e was nil
                          blast,
                          -- if e was a path
                          blast,
                          rewrite C.associativity,
                          refine ( congr_arg (C.compose e) _ ),
                          exact ih_2 l_1 ih_1
                        end
}

end tqft.categories.n_ary
