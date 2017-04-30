-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ...monoidal_categories.monoidal_category
import ...discrete_category
import ...universal.categories

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

definition TensorProductOfCategories : TensorProduct CategoryOfCategoriesAndFunctors.{u v} := {
    onObjects     := λ p, ProductCategory p.1 p.2,
    onMorphisms   := λ _ _ p, ProductFunctor p.1 p.2,
    identities    := ♯,
    functoriality := ♮
  }

definition CategoryAssociator : Associator TensorProductOfCategories.{u v} := {
    morphism := {
      components := λ t, ProductCategoryAssociator t.1.1 t.1.2 t.2,
      naturality := ♮
    },
    inverse := {
      components := λ t, ProductCategoryInverseAssociator t.1.1 t.1.2 t.2,
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  }

definition CategoryTensorUnit := DiscreteCategory.{u v} punit

definition CategoryLeftUnitor : @LeftUnitor CategoryOfCategoriesAndFunctors.{u v} CategoryTensorUnit TensorProductOfCategories := {
  morphism := {
    components := λ p, RightProjection _ p,
    naturality := ♮
  },
  inverse := {
    components := λ t, LeftInjectionAt punit.star t,
    naturality := ♮
  },
  witness_1 := ♯,
  witness_2 := ♯
}

definition CategoryRightUnitor : @RightUnitor CategoryOfCategoriesAndFunctors.{u v} CategoryTensorUnit TensorProductOfCategories := {
  morphism := {
    components := λ p, LeftProjection p _,
    naturality := ♮
  },
  inverse := {
    components := λ t, RightInjectionAt punit.star t,
    naturality := ♮
  },
  witness_1 := ♯,
  witness_2 := ♯
}

definition CartesianProductOfCategories : MonoidalStructure CategoryOfCategoriesAndFunctors.{u v} := {
  tensor      := TensorProductOfCategories,
  tensor_unit := CategoryTensorUnit,
  associator_transformation := CategoryAssociator,
  left_unitor  := CategoryLeftUnitor,
  right_unitor := CategoryRightUnitor,
  pentagon := ♯,
  triangle := ♯
}

end tqft.categories.monoidal_category