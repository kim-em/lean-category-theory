-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .enriched_category
import .examples.categories.cartesian_product

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.enriched
open tqft.categories.monoidal_category

namespace tqft.categories.two_category_1

-- universe variables u v

definition {v w} TwoCategory := EnrichedCategory.{(max (v+1) (w+1))} CartesianProductOfCategories.{v w}

-- PROJECT test if this is viable --- construct examples, etc.

set_option pp.all true

#check TwoCategory
#check CategoryOfCategoriesAndFunctors

definition {v w} CAT : TwoCategory.{v w} :=
{
    Obj := Category.{v w},
    Hom := λ C D, ⟦ FunctorCategory C D ⟧,
    compose  := λ _ _ _ F G, sorry,
    identity := sorry,
    left_identity := sorry,
    right_identity := sorry,
    associativity := sorry
}  

end tqft.categories.two_category_1