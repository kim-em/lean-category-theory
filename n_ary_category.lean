-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

import .graph
import .category

open tqft.categories.graph

namespace tqft.categories.n_ary

@[reducible] definition {u v} compose_each_path
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
  (associativity : ∀ { X Y Z : graph.vertices } (p : path X Y) (q : path Y Z), compose (concatenate_paths p q) = (compose p[ compose p, compose q ]) )

attribute [simp,ematch] n_ary_Category.compose_empty_path
attribute [simp,ematch] n_ary_Category.compose_length_one_path
attribute [simp,ematch] n_ary_Category.associativity

lemma n_ary_Category.associativity' { C: n_ary_Category } { X Y Z : C.graph.vertices } ( e : C.graph.edges X Y ) ( p : path Y Z ) : C.compose ( e :: p ) = (C.compose p[ e, C.compose p ]) :=
begin
  rewrite - C.compose_length_one_path e,
  rewrite - C.associativity,
  blast
end

lemma n_ary_Category.associativity'' { C: n_ary_Category } { X Y : C.graph.vertices } ( p : path_of_paths X Y ) :
    C.compose (@compose_each_path C.graph (@n_ary_Category.compose C) X Y p) = C.compose (concatenate_path_of_paths p) :=
    begin
      induction p,
      blast,
      unfold compose_each_path._main,
      unfold concatenate_path_of_paths,
      rewrite C.associativity,
      rewrite - ih_1,
      unfold compose_each_path._main,
      apply n_ary_Category.associativity'
    end

open tqft.categories

definition {u v} compose_path
  { G : Graph.{u v} }
  { identity : Π X : G.vertices, G.edges X X }
  { composition : Π { A B C : G.vertices }, G.edges A B → G.edges B C → G.edges A C } :
   Π { X Y : G.vertices }, path X Y → G.edges X Y
| ._ ._ (path.nil X) := identity X
| ._ ._ (@path.cons ._ _ _ _ e p) := composition e (compose_path p)


-- FIXME this is a bit lame.
meta def rewrite_once : tactic unit :=
do r ← tactic.to_expr `(n_ary_Category.compose_length_one_path C f),
   tactic.rewrite_core reducible tt tt (occurrences.pos [2]) tt r


definition {u v} n_ary_Category_to_Category ( C: n_ary_Category.{u v} ) : Category :=
{
  Obj := C.graph.vertices,
  Hom := C.graph.edges,
  identity := C.identity,
  compose := λ X Y Z f g, C.compose ( p[ f, g ] ),
  left_identity  := begin
                      intros,
                      rewrite - C.compose_empty_path, 
                      rewrite - C.compose_length_one_path f,  
                      rewrite - C.associativity,
                      blast
                    end,
  right_identity := begin
                      intros,
                      rewrite - C.compose_empty_path, 
                      rewrite - C.compose_length_one_path f,  
                      rewrite - C.associativity,
                      blast                    
                    end,
  associativity  := begin
                      intros,
                      rewrite - C.compose_length_one_path h,
                      rewrite - C.associativity,
                      unfold_unfoldable,
                      rewrite_once,
                      rewrite - C.associativity,
                      unfold_unfoldable
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
                          unfold graph.concatenate_paths,
                          unfold compose_path,
                          rewrite ih_1 q,
                          blast
                        end
}

end tqft.categories.n_ary
