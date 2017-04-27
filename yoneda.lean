-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .opposites
import .equivalence
import .examples.types.types

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.equivalence
open tqft.categories.examples.types

namespace tqft.categories.yoneda

local attribute [pointwise] funext

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

theorem {u v} YonedaEmbedding ( C : Category.{u v} ) : Embedding (Yoneda C) :=
begin
  blast,
  {
    -- Show it is full
    fsplit,
    {
        intros,
        exact (f.components X) (C.identity X)
    },
    {
        blast,   
        admit
    }
  },
  {
    -- Show it is faithful
    fsplit,
    unfold_unfoldable,
    intros,
    pose q := congr_arg NaturalTransformation.components p,
    simp at q,
    pose q' := congr_fun q X,
    simp at q',
    pose q'' := congr_fun q' (C.identity X),
    simp at q'',
    exact q''
  }
end

end tqft.categories.yoneda