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
    identities    := ♮,
    functoriality := ♯
}

theorem {u v} YonedaEmbedding ( C : Category.{u v} ) : Embedding (Yoneda C) :=
begin
  unfold Embedding,
  unfold Yoneda,
  split,
  -- First we show it is full.
  begin
    unfold Full,
    intros,
    unfold Surjective,
    refine ⟨ _, _ ⟩,  -- we ned to build a preimage, which is expressed as a subtype.
    -- Now we have to construct the preimage
    begin
        intros,
        unfold FunctorCategory at a,
        simp at a,
        exact (a.components X) (C.identity X), -- <-- this is a critical step for surjectivity
    end,
    -- then verify that it really is a preimage
    begin
        blast
    end,
  end,
  -- Second we show it is faithful.
  begin
    unfold Faithful,
    intros,
    unfold Injective,
    split,
    intros X Y f g,
    simp,
    intros a,
    pose p := congr_arg (λ T, NaturalTransformation.components T) a,
    simp at p,
    pose p' := congr_fun p X,
    simp at p',
    pose p'' := congr_fun p' (C.identity X),
    simp at p'',
    exact p''
  end
end

end tqft.categories.yoneda