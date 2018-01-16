-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .isomorphism
import .opposites
import .equivalence
import .products.switch
import .types

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.isomorphism
open categories.equivalence
open categories.types
open categories.products
open categories.opposites

namespace categories.yoneda

definition {u v} Yoneda ( C : Category.{u v} ) : Functor C (FunctorCategory (Opposite C) CategoryOfTypes.{v}) :=
{
    onObjects := λ X, {
        onObjects     := λ Y, C.Hom Y X,
        onMorphisms   := λ Y Y' f, λ g, C.compose f g
    },
    onMorphisms   := λ X X' f, {
        components := λ Y, λ g, C.compose g f
    }
}

@[reducible] definition {v} YonedaEvaluation ( C : Category.{v v} )
  : Functor (ProductCategory (FunctorCategory (Opposite C) CategoryOfTypes.{v}) (Opposite C)) CategoryOfTypes.{v}
  := Evaluation (Opposite C) CategoryOfTypes.{v}
@[reducible] definition {v} YonedaPairing ( C : Category.{v v} ) 
  : Functor (ProductCategory (FunctorCategory (Opposite C) CategoryOfTypes.{v}) (Opposite C)) CategoryOfTypes.{v}
  := FunctorComposition
      (FunctorComposition
        (ProductFunctor (IdentityFunctor _) (OppositeFunctor (Yoneda C)))
        (SwitchProductCategory _ _))
      (HomPairing (FunctorCategory (Opposite C) CategoryOfTypes.{v})) 

@[simp] private lemma YonedaLemma_aux_1
   { C : Category }
   { X Y : C.Obj }
   ( f : C.Hom X Y )
   { F G : Functor (Opposite C) CategoryOfTypes }
   ( τ : NaturalTransformation F G )
   ( Z : F.onObjects Y ) :
     G.onMorphisms f (τ.components Y Z) = τ.components X (F.onMorphisms f Z) := eq.symm (congr_fun (τ.naturality f) Z)

-- FIXME restore this
-- theorem {v} YonedaLemma ( C : Category.{v v} ) : NaturalIsomorphism (YonedaPairing C) (YonedaEvaluation C) := 
-- begin
--   tidy {hints:=[9, 8, 9, 8, 7, 9, 7, 12, 11, 9, 12, 17, 18, 17, 18, 17, 18, 17, 18, 20, 18, 17, 18, 19, 18, 20, 18, 17, 18, 17, 18, 17, 18, 19, 18, 20, 18, 17, 18, 20, 22, 20, 23, 22, 20, 23]},
--   exact ((a.components _) (C.identity _)),
--   tidy {hints:=[9, 10, 20]},
--   exact ((X_fst.onMorphisms a_1) a),
--   tidy,
-- end

-- theorem {u v} YonedaEmbedding ( C : Category.{u v} ) : Embedding (Yoneda C) :=
-- begin
--   unfold Embedding,
--   fsplit,
--   {
--     -- Show it is full
--     fsplit,
--     {
--         tidy,
--         exact (f.components X) (C.identity X)
--     },
--     {
--         tidy,
--         have q := congr_fun (f.naturality x) (C.identity X),
--         tidy,
--     }
--   },
--   {
--     -- Show it is faithful
--     tidy,
--     have q := congr_arg NaturalTransformation.components p,
--     have q' := congr_fun q X,
--     have q'' := congr_fun q' (C.identity X),
--     tidy,
--   }
-- end

end categories.yoneda