-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..adjunctions
import .hom_adjunction

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.isomorphism
open categories.types

namespace categories.adjunctions

definition Adjunction_to_HomAdjunction  { C D : Category } { L : Functor C D } { R : Functor D C } ( A : Adjunction L R ) : HomAdjunction L R := 
{
    morphism  := {
      components := λ P, 
        -- We need to construct the map from D.Hom (L P.1) P.2 to C.Hom P.1 (R P.2)
        λ f, C.compose (A.unit.components P.1) (R.onMorphisms f),
      naturality := begin
                      tidy,
                      repeat_at_least_once { rewrite - C.associativity },
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
                      repeat_at_least_once { rewrite D.associativity },
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

@[reducible] private definition unit_from_HomAdjunction { C D : Category } { L : Functor C D } { R : Functor D C } ( A : HomAdjunction L R ) : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) := {
    components := λ X : C.Obj, A.morphism.components (X, L.onObjects X) (D.identity (L.onObjects X)),
    naturality := begin
                    tidy,
                    have p := @NaturalTransformation.naturality _ _ _ _ A.morphism (X, L X) (X, L Y) (C.identity X, L.onMorphisms f),--((Opposite C × D).identity (X, L Y)),
                    tidy,
                    have q := congr_fun p (L.onMorphisms (C.identity X)), -- PROJECT extract q as a lemma about mates
                    tidy,
                    rewrite - q,
                    clear p q,                   
                    -- FIXME leaving off .onObjects in the following line causes tidy to run forever, because of 'has_coe_to_fun.coe'
                    have p := @NaturalTransformation.naturality _ _ _ _ A.morphism (Y, L.onObjects Y) (X, L.onObjects Y) (f, D.identity (L.onObjects Y)),--((Opposite C × D).identity (X, L Y)),
                    tidy,
                    have q := congr_fun p (L.onMorphisms (C.identity Y)), -- PROJECT extract q as a lemma about mates
                    tidy,
                    rewrite - q,
                  end
  }
@[reducible] private definition counit_from_HomAdjunction { C D : Category } { L : Functor C D } { R : Functor D C } ( A : HomAdjunction L R ) : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) := {
    components := λ X : D.Obj, A.inverse.components (R.onObjects X, X) (C.identity (R.onObjects X)),
    naturality := begin
                    tidy,
                    have p := @NaturalTransformation.naturality _ _ _ _ A.inverse (R.onObjects Y, Y) (R.onObjects X, Y) (R.onMorphisms f, D.identity Y),--((Opposite C × D).identity (X, L Y)),
                    tidy,
                    have q := congr_fun p (R.onMorphisms (D.identity Y)), -- PROJECT extract q as a lemma about mates
                    tidy,
                    rewrite - q,
                    clear p q,                   
                    -- FIXME leaving off .onObjects in the following line causes tidy to run forever, because of 'has_coe_to_fun.coe'
                    have p := @NaturalTransformation.naturality _ _ _ _ A.inverse (R.onObjects X, X) (R.onObjects X, Y) (C.identity (R.onObjects X), f),--((Opposite C × D).identity (X, L Y)),
                    tidy,
                    have q := congr_fun p (R.onMorphisms (D.identity X)), -- PROJECT extract q as a lemma about mates
                    tidy,
                    rewrite - q,
                  end
  }

definition HomAdjunction_to_Adjunction { C D : Category } { L : Functor C D } { R : Functor D C } ( A : HomAdjunction L R ) : Adjunction L R := 
{
  unit       := unit_from_HomAdjunction A,
  counit     := counit_from_HomAdjunction A,
  triangle_1 := begin
                  intros,
                  simp,
                  have p := A.witness_1,
                  have q := @NaturalTransformation.naturality _ _ _ _ A.morphism (R.onObjects X, X) (R.onObjects X, X) (C.identity (R.onObjects X), D.identity X),
                  tidy,
                  admit
                end,
  triangle_2 := sorry
}

definition Adjunctions_agree { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :
  Isomorphism CategoryOfTypes (Adjunction L R) (HomAdjunction L R) := 
{
  morphism  := Adjunction_to_HomAdjunction,
  inverse   := HomAdjunction_to_Adjunction,
  witness_1 := begin tidy, end,
  witness_2 := begin
                 tidy,
                 -- this is just another lemma about mates; perhaps the same as the one we use above.
               end
}

end categories.adjunctions