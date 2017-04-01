-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .enriched_category
import ..examples.categories.cartesian_product

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.enriched
open tqft.categories.products
open tqft.categories.monoidal_category

namespace tqft.categories.two_category_1

definition {u} TwoCategory := EnrichedCategory CartesianProductOfCategories.{u u}

@[unfoldable] definition horizontal_composition_on_FunctorCategories { C D E : Category } : Functor (ProductCategory (FunctorCategory C D) (FunctorCategory D E)) (FunctorCategory C E) :=
{
    onObjects     := λ p, FunctorComposition p.1 p.2,
    onMorphisms   := λ _ _ p, horizontal_composition_of_NaturalTransformations p.1 p.2,
    identities    := ♯,
    functoriality := ♯
}

definition {u} CAT : TwoCategory.{u} :=
{
    Obj            := Category.{u u},
    Hom            := λ C D, FunctorCategory C D,
    compose        := λ _ _ _, horizontal_composition_on_FunctorCategories,
    identity       := λ C, { onObjects := λ _, IdentityFunctor C, onMorphisms := λ _ _ _, IdentityNaturalTransformation (IdentityFunctor C), identities := ♮, functoriality := ♯ },
    left_identity  := ♯,
    right_identity := ♮,
    associativity  := ♮
}  

-- PROJECT strict n-categories; for this we'll need to define products of enriched categories, and show that (n-1) categories are symmetric.

end tqft.categories.two_category_1