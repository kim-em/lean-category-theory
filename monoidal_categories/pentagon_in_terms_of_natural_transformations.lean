-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

--set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

@[reducible] definition pentagon_3step_1 ( C : MonoidalCategory.{ u v } ) :=
  let α := C^.associator_transformation in
  whisker_on_right
    (α × IdentityNaturalTransformation (IdentityFunctor C))
    C^.tensor

@[reducible] definition pentagon_3step_2 ( C : MonoidalCategory.{ u v } ) :=
  let α := C^.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      ((IdentityFunctor C × C^.tensor) × IdentityFunctor C))
    α

@[reducible] definition pentagon_3step_3 ( C : MonoidalCategory.{ u v } ) :=
  let α := C^.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      (ProductCategoryAssociator C (C × C) C))
    (whisker_on_right
      (IdentityNaturalTransformation (IdentityFunctor C) × α)
      C^.tensor)

@[reducible] definition pentagon_3step ( C : MonoidalCategory.{ u v } ) :=
  vertical_composition_of_NaturalTransformations
    (vertical_composition_of_NaturalTransformations
      (pentagon_3step_1 C)
      (pentagon_3step_2 C))
    (pentagon_3step_3 C)

@[reducible] definition pentagon_2step_1 ( C : MonoidalCategory.{ u v } ) :=
  let α := C^.associator_transformation in
  whisker_on_left
    ((C^.tensor × IdentityFunctor C) × IdentityFunctor C)
    α

@[reducible] definition pentagon_2step_2 ( C : MonoidalCategory.{ u v } ) :=
  let α := C^.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator (C × C) C C)
      (IdentityFunctor (C × C) × C^.tensor))
    α

@[reducible] definition pentagon_2step ( C : MonoidalCategory.{ u v } ) :=
  vertical_composition_of_NaturalTransformations
    (pentagon_2step_1 C)
    (pentagon_2step_2 C)

end tqft.categories.monoidal_category