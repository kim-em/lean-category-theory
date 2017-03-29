-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

@[reducible] definition pentagon_3step_1 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m^.associator_transformation in
  whisker_on_right
    (α × IdentityNaturalTransformation (IdentityFunctor C))
    m^.tensor

@[reducible] definition pentagon_3step_2 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m^.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      ((IdentityFunctor C × m^.tensor) × IdentityFunctor C))
    α

@[reducible] definition pentagon_3step_3 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m^.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      (ProductCategoryAssociator C (C × C) C))
    (whisker_on_right
      (IdentityNaturalTransformation (IdentityFunctor C) × α)
      m^.tensor)

@[reducible] definition pentagon_3step { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  vertical_composition_of_NaturalTransformations
    (vertical_composition_of_NaturalTransformations
      (pentagon_3step_1 m)
      (pentagon_3step_2 m))
    (pentagon_3step_3 m)

@[reducible] definition pentagon_2step_1 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m^.associator_transformation in
  whisker_on_left
    ((m^.tensor × IdentityFunctor C) × IdentityFunctor C)
    α

@[reducible] definition pentagon_2step_2 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m^.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator (C × C) C C)
      (IdentityFunctor (C × C) × m^.tensor))
    α

@[reducible] definition pentagon_2step { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  vertical_composition_of_NaturalTransformations
    (pentagon_2step_1 m)
    (pentagon_2step_2 m)

end tqft.categories.monoidal_category