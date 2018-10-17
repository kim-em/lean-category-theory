-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import category_theory.category
import category_theory.graphs

namespace category_theory

open category_theory.graphs

universes u v
variable {C : Type u}

instance category.graph [𝒞 : category.{u v} C] : graph C := {
  edges := 𝒞.hom
}

variable [small_category C]

inductive morphism_path : C → C → Type (u+1)
| nil  : Π (h : C), morphism_path h h
| cons : Π {h s t : C} (e : h ⟶ s) (l : morphism_path s t), morphism_path h t

notation a :: b := morphism_path.cons a b
notation `c[` l:(foldr `, ` (h t, morphism_path.cons h t) morphism_path.nil _ `]`) := l

def concatenate_paths : Π {x y z : C}, morphism_path x y → morphism_path y z → morphism_path x z
| ._ ._ _ (morphism_path.nil _)                 q := q
| ._ ._ _ (@morphism_path.cons ._ _ _ _ _ e p') q := morphism_path.cons e (concatenate_paths p' q)

def category.compose_path : Π {X Y : C}, morphism_path X Y → (X ⟶ Y)
| X ._  (morphism_path.nil ._)                 := 𝟙 X
| _ _   (@morphism_path.cons ._ ._ _ _ ._ e p) := e ≫ (category.compose_path p)

end category_theory