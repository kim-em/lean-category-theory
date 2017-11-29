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

namespace categories.yoneda

definition {u v} Yoneda ( C : Category.{u v} ) : Functor C (FunctorCategory (Opposite C) CategoryOfTypes.{v}) :=
{
    onObjects := λ X, {
        onObjects     := λ Y, C.Hom Y X,
        onMorphisms   := λ Y Y' f, λ g, C.compose f g,
        identities    := ♯,
        functoriality := ♯ 
    },
    onMorphisms   := λ X X' f, {
        components := λ Y, λ g, C.compose g f,
        naturality := ♯
    },
    identities    := ♯,
    functoriality := ♯
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

theorem {v} YonedaLemma ( C : Category.{v v} ) : NaturalIsomorphism (YonedaPairing C) (YonedaEvaluation C) := 
begin
  tidy {hints:=[8, 7, 8, 7, 6, 8, 6, 11, 10, 8, 11, 15, 16, 15, 16, 15, 16, 15, 16, 18, 17, 16, 15, 16, 15, 16, 15, 16, 18, 16, 17, 16, 15, 16, 18, 16, 21, 20, 18, 21]},
  exact ((a.components _) (C.identity _)),
  tidy {hints:=[2, 8, 9]},
  exact ((fst.onMorphisms a_1) a),
  tidy {hints:=[2, 9, 3, 2, 9, 3, 2, 9, 2, 9, 3]},
end

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