-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_categories.monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

definition CategoryOfCategoriesAndFunctorsWithCartesianProduct : MonoidalCategory := {
  CategoryOfCategoriesAndFunctors with
  tensor      := sorry,
  tensor_unit := sorry,
  associator_transformation := sorry,
  left_unitor  := sorry,
  right_unitor := sorry,
  pentagon := sorry,
  triangle := sorry,
  associator_is_isomorphism   := sorry,
  left_unitor_is_isomorphism  := sorry,
  right_unitor_is_isomorphism := sorry
}

end tqft.categories.monoidal_category