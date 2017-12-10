-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

import .graphs
import .category

open categories.graphs

namespace categories.n_ary

@[reducible] definition {u v} compose_each_path
  { G : Graph.{u v} }
  { composition : Π { A B : G.Obj }, path A B → G.Hom A B } :
   Π { X Y : G.Obj }, path_of_paths X Y → path X Y
| ._ ._ (path_of_paths.nil X) := path.nil X
| ._ ._ (@path_of_paths.cons ._ _ _ _ p ps) := path.cons (composition p) (compose_each_path ps)

structure {u v} n_ary_Category extends graph : Graph.{u v} :=
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y : Obj }, path X Y → Hom X Y)
  (compose_empty_path  : ∀ ( X : Obj ), compose ( p[] ) = identity X)
  (compose_length_one_path : ∀ { X Y : Obj } ( f : Hom X Y ), compose ( p[f] ) = f )
  (associativity : ∀ { X Y Z : Obj } (p : path X Y) (q : path Y Z), compose (concatenate_paths p q) = (compose p[ compose p, compose q ]) )

attribute [simp,ematch] n_ary_Category.compose_empty_path
attribute [simp,ematch] n_ary_Category.compose_length_one_path
attribute [simp,ematch] n_ary_Category.associativity

-- lemma n_ary_Category.associativity' { C: n_ary_Category } { X Y Z : C.Obj } ( e : C.Hom X Y ) ( p : path Y Z ) : C.compose ( e :: p ) = (C.compose p[ e, C.compose p ]) :=
-- begin
--   rewrite ← C.compose_length_one_path e,
--   rewrite ← C.associativity,
--   blast,
--   admit
-- end

-- lemma n_ary_Category.associativity'' { C: n_ary_Category } { X Y : C.Obj } ( p : path_of_paths X Y ) :
--     C.compose (@compose_each_path C.graph (@n_ary_Category.compose C) X Y p) = C.compose (concatenate_path_of_paths p) :=
--     begin
--       induction p,
--       blast,
--       unfold compose_each_path._main,
--       unfold concatenate_path_of_paths,
--       rewrite C.associativity,
--       rewrite ← ih_1,
--       unfold compose_each_path._main,
--       apply n_ary_Category.associativity'
--     end

open categories

definition {u v} compose_path
  { G : Graph.{u v} }
  { identity : Π X : G.Obj, G.Hom X X }
  { composition : Π { A B C : G.Obj }, G.Hom A B → G.Hom B C → G.Hom A C } :
   Π { X Y : G.Obj }, path X Y → G.Hom X Y
| ._ ._ (path.nil X) := identity X
| ._ ._ (@path.cons ._ _ _ _ e p) := composition e (compose_path p)

definition {u v} n_ary_Category_to_Category ( C: n_ary_Category.{u v} ) : Category :=
{
  Obj := C.graph.Obj,
  Hom := C.graph.Hom,
  identity := C.identity,
  compose := λ X Y Z f g, C.compose ( p[ f, g ] ),
  left_identity  := begin
                      intros,
                      rewrite ← C.compose_empty_path, 
                      rewrite ← C.compose_length_one_path f,  
                      rewrite ← C.associativity,
                      blast
                    end,
  right_identity := begin
                      intros,
                      rewrite ← C.compose_empty_path, 
                      rewrite ← C.compose_length_one_path f,  
                      rewrite ← C.associativity,
                      blast                    
                    end,
  associativity  := begin
                      intros,
                      rewrite ← C.compose_length_one_path h,
                      rewrite ← C.associativity,
                      unfold graphs.concatenate_paths,
                      conv { for (f) [2] { rewrite ← n_ary_Category.compose_length_one_path C f }},
                      rewrite ← C.associativity,
                      unfold graphs.concatenate_paths,
                      rewrite C.compose_length_one_path
                    end
}

-- PROJECT fix this
-- definition {u v} Category_to_n_ary_Category ( C : Category.{u v} ) : n_ary_Category :=
-- {
--   graph := C.graph,
--   identity := λ X, C.identity X,
--   compose  := λ X Y f, @compose_path C.graph (C.identity) (@Category.compose C) X Y f,
--   compose_empty_path := ♯,
--   compose_length_one_path := begin tidy, admit end,
--   associativity      := begin
--                           blast,
--                           induction p,
--                           { -- if p was nil
--                             blast,
--                             admit
--                           },
--                           { -- if p was a path
--                             unfold graphs.concatenate_paths,
--                             unfold compose_path,
--                             rewrite ih_1 q,
--                             blast
--                           }
--                         end
-- }

end categories.n_ary
