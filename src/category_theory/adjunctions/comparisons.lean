-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .adjunction
import .hom_adjunction

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.isomorphism
open tqft.categories.types

namespace tqft.categories.adjunction

definition Adjunction_to_HomAdjunction  { C D : Category } ( L : Functor C D ) ( R : Functor D C ) ( A : Adjunction L R ) : HomAdjunction L R := 
{
    morphism  := {
      components := λ P, 
        -- We need to construct the map from D.Hom (L P.1) P.2 to C.Hom P.1 (R P.2)
        λ f, C.compose (A.unit.components P.1) (R.onMorphisms f),
      naturality := begin
                      tidy,
                      repeat { rewrite - C.associativity },
                      rewrite A.unit_naturality
                    end
    },
    inverse   := 
    {
      components := λ P, 
        -- We need to construct the map back to D.Hom (L P.1) P.2 from C.Hom P.1 (R P.2)
        λ f, D.compose (L.onMorphisms f) (A.counit.components P.2),
      naturality := begin
                      tidy,
                      repeat { rewrite D.associativity },
                      rewrite - A.counit_naturality
                    end
    },
    witness_1 := begin
                   tidy,
                   rewrite D.associativity,
                   rewrite A.counit_naturality,
                   rewrite - D.associativity,
                   rewrite A.triangle_2,
                   simp
                 end,
    witness_2 := begin
                   tidy,
                   rewrite - C.associativity,
                   rewrite - A.unit_naturality,
                   rewrite C.associativity,
                   rewrite A.triangle_1,
                   simp
                 end
  }


-- lemma triangle_1_lemma { C D : Category } ( L : Functor C D ) ( R : Functor D C ) ( A : HomAdjunction L R ) ( X : D.Obj ) :
--   C.compose ((A.morphism).components (R X, L (R X)) (D.identity (L (R X))))
--     (R.onMorphisms ((A.inverse).components (R X, X) (C.identity (R X)))) = C.identity (R X) :=
--   begin
--     pose q := @NaturalTransformation.naturality _ _ _ _ A.morphism _ _ ((Opposite C × D).identity (R X, X)),
--     pose q' := @NaturalTransformation.naturality _ _ _ _ A.inverse _ _ ((Opposite C × D).identity (R X, X)),
    
--     pose p := congr_fun q' (C.identity (R X)),
    
--   end

-- definition HomAdjunction_to_Adjunction  { C D : Category } ( L : Functor C D ) ( R : Functor D C ) ( A : HomAdjunction L R ) : Adjunction L R := 
-- {
--   unit       := {
--     components := λ X : C.Obj, A.morphism.components (X, L.onObjects X) (D.identity (L.onObjects X)),
--     naturality := begin
--                     intros,
--                     unfold_projections,
--                     dsimp,
--                     have p := @NaturalTransformation.naturality _ _ _ _ A.morphism (X, L X) (X, L Y) (C.identity X, L.onMorphisms f),--((Opposite C × D).identity (X, L Y)),
--                     unfold_projections_hypotheses,
--                     dsimp_hypotheses,
--                     unfold_projections_hypotheses,
--                     dsimp_hypotheses,
--                     unfold_projections_hypotheses,
--                     dsimp_hypotheses,
--                     have q := congr_fun p (L.onMorphisms (C.identity X)),
--                     dsimp at q,
--                     rewrite C.left_identity at q,
--                     rewrite L.identities at q,
--                     rewrite D.left_identity at q,
--                     rewrite D.left_identity at q,
--                     rewrite - q,
                    
--                     admit 
--                   end
--   },
--   counit     := {
--     components := λ X : D.Obj, A.inverse.components (R.onObjects X, X) (C.identity (R.onObjects X)),
--     naturality := sorry
--   },
--   triangle_1 := begin
--                   intros,
--                   simp,
--                   pose p := A.witness_1,
--                   -- pose q := A.morphism.naturality (C.identity (R.onObjects X), D.identity X),
--                   admit
--                 end,
--   triangle_2 := sorry
-- }

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