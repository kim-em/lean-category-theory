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

lemma triangle_1_lemma { C D : Category } ( L : Functor C D ) ( R : Functor D C ) ( A : HomAdjunction L R ) ( X : D.Obj ) :
  C.compose ((A.morphism).components (R X, L (R X)) (D.identity (L (R X))))
    (R.onMorphisms ((A.inverse).components (R X, X) (C.identity (R X)))) = C.identity (R X) :=
  begin
    pose q := @NaturalTransformation.naturality _ _ _ _ A.morphism _ _ ((Opposite C × D).identity (R X, X)),
    pose q' := @NaturalTransformation.naturality _ _ _ _ A.inverse _ _ ((Opposite C × D).identity (R X, X)),
    
    pose p := congr_fun q' (C.identity (R X)),
    
  end

-- definition HomAdjunction_to_Adjunction  { C D : Category } ( L : Functor C D ) ( R : Functor D C ) ( A : HomAdjunction L R ) : Adjunction L R := 
-- {
--   unit       := {
--     components := λ X : C.Obj, A.morphism.components (X, L X) (D.identity (L X)),
--     naturality := begin
--                     -- intros, 
--                     -- unfold_unfoldable_goals, 
                    
--                     admit 
--                   end
--   },
--   counit     := {
--     components := λ X : D.Obj, A.inverse.components (R X, X) (C.identity (R X)),
--     naturality := sorry
--   },
--   triangle_1 := begin
--                   intros,
--                   simp,
--                   pose p := A.witness_1,
--                   pose q := A.morphism.naturality (C.identity (R X), D.identity X),
--                   admit
--                 end,
--   triangle_2 := sorry
-- }

-- local attribute [pointwise] funext

-- definition Adjunctions_agree { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :
--   Isomorphism CategoryOfTypes (Adjunction L R) (HomAdjunction L R) := 
-- {
--   morphism  := Adjunction_to_HomAdjunction L R,
--   inverse   := HomAdjunction_to_Adjunction L R,
--   witness_1 := ♯,
--   witness_2 := begin
--                  blast,
                 
--                end
-- }

end tqft.categories.adjunction