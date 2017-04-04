-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .adjunction

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.isomorphism
open tqft.categories.examples.types

namespace tqft.categories.adjunction

@[unfoldable] definition HomAdjunction_to_Adjunction  { C D : Category } ( L : Functor C D ) ( R : Functor D C ) ( A : HomAdjunction L R ) : Adjunction L R := 
{
  unit       := {
    components := λ X : C.Obj, A.morphism.components (X, L X) (D.identity (L X)),
    naturality := begin
                    -- intros, 
                    -- unfold_unfoldable_goals, 
                    
                    admit 
                  end
  },
  counit     := {
    components := λ X : D.Obj, A.inverse.components (R X, X) (C.identity (R X)),
    naturality := sorry
  },
  triangle_1 := begin
                  intros,
                  simp,
                  admit
                end,
  triangle_2 := sorry
}

local attribute [pointwise] funext

definition Adjunctions_agree { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :
  Isomorphism CategoryOfTypes (Adjunction L R) (HomAdjunction L R) := 
{
  morphism  := Adjunction_to_HomAdjunction L R,
  inverse   := HomAdjunction_to_Adjunction L R,
  witness_1 := ♯,
  witness_2 := begin
                 blast,
                 
               end
}

end tqft.categories.adjunction