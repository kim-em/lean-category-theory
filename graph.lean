-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .category

open tqft.categories

structure {u v} Graph :=
  ( vertices : Type u )
  ( edges : vertices → vertices → Type v )

inductive {u v} path { G : Graph.{u v} } : Graph.vertices G → Graph.vertices G → list G^.vertices → Type (max u v)
| nil  : Π (x : G^.vertices), path x x [x]
| cons : Π {x y z: G^.vertices} {l : list G^.vertices}, G^.edges x y → path y z l → path x z (x::l)

definition {u v} path_between { G : Graph.{u v} } ( x : G^.vertices ) ( y : G^.vertices ) : Type (max u v)
  := Σ l : list G^.vertices, path x y l

definition concatenate_paths
 { G : Graph }
 { x y z : G^.vertices }
 { l : list G^.vertices }
 { m : list G^.vertices }
 ( p : path x y l )
 ( q : path y z m )
  : path x z (l ++ m.tail)
  := match q with
     | path.nil y     := q
     | path.cons e p' := path.cons e (concatenate_paths p' q)

definition concatenate_paths_between
  { G : Graph }
  { x y z : G^.vertices } 
  ( p : path_between x y ) 
  ( q: path_between y z ) 
   : path_between x z 
   := ⟨ p.1 ++ q.1.tail, concatenate_paths p.2 q.2 ⟩

instance path_coercion_to_path_between { G : Graph } { x y : G^.vertices } { l : list G^.vertices } : has_coe (path x y l) (path_between x y) :=
  { coe := λ p, ⟨ l, p ⟩ }

definition PathCategory ( G : Graph ) : Category :=
{
  Obj            := G^.vertices,
  Hom            := λ x y, path_between x y,
  identity       := λ x, path.nil x,
  compose        := λ _ _ _ f g, concatenate_paths_between f g,
  left_identity  := sorry,
  right_identity := sorry,
  associativity  := sorry
}