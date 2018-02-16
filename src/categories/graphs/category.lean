-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import ..category
import ..graphs

namespace categories

open categories.graphs

universe u
variable {C : Type u}

instance category.graph [𝓒 : category C] : graph C := {
  edges := 𝓒.Hom
}

variable [category C]

inductive morphism_path : C → C → Type u
| nil  : Π (h : C), morphism_path h h
| cons : Π {h s t : C} (e : Hom h s) (l : morphism_path s t), morphism_path h t

notation a :: b := morphism_path.cons a b
notation `c[` l:(foldr `, ` (h t, morphism_path.cons h t) morphism_path.nil _ `]`) := l

definition concatenate_paths : Π {x y z : C}, morphism_path x y → morphism_path y z → morphism_path x z
| ._ ._ _ (morphism_path.nil _)               q := q
| ._ ._ _ (@morphism_path.cons ._ _ _ _ _ e p') q := morphism_path.cons e (concatenate_paths p' q)

definition category.compose_path : Π {X Y : C}, morphism_path X Y → Hom X Y
| X ._  (morphism_path.nil ._)                := 𝟙 X
| _ _   (@morphism_path.cons ._ ._ _ _ ._ e p)  := e >> (category.compose_path p)

end categories