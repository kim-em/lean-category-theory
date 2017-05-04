-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .isomorphism
import .opposites
import .equivalence
import .products.products
import .products.switch
import .examples.types.types

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.equivalence
open tqft.categories.examples.types
open tqft.categories.products

namespace tqft.categories.yoneda

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

-- PROJECT finish this
theorem {v} YonedaLemma ( C : Category.{v v} ) : NaturalIsomorphism (YonedaPairing C) (YonedaEvaluation C) := sorry
-- begin
--   unfold NaturalIsomorphism,
--   fsplit,
--   {
--     unfold FunctorCategory,
--     dsimp,
--     fsplit,
--     {
--       tidy,
--       exact ((a.components X_2) (C.identity X_2))
--     },
--     {
--       tidy,
--       pose p := x.naturality f_2,
--       unfold_projections at p,
--       simp at p,
--       pose q := congr_fun p (C.identity X_2),
--       rewrite composition at q,
--       simp at q,
--       tidy,
--       rewrite q
--     }
--   },
--   {
--     tidy,
--     admit
--   },
--   {
--     tidy,
--     admit
--   },
--   {
--     tidy,
--     admit
--   }
-- end


theorem {u v} YonedaEmbedding ( C : Category.{u v} ) : Embedding (Yoneda C) :=
begin
  unfold Embedding,
  fsplit,
  {
    -- Show it is full
    fsplit,
    {
        tidy,
        exact (f.components X) (C.identity X)
    },
    {
        tidy,
        note p := f.naturality x,
        tidy,
        note q := congr_fun p (C.identity X),
        blast
    }
  },
  {
    -- Show it is faithful
    fsplit,
    tidy,
    note q := congr_arg NaturalTransformation.components p,
    note q' := congr_fun q X,
    note q'' := congr_fun q' (C.identity X),
    blast
  }
end

end tqft.categories.yoneda