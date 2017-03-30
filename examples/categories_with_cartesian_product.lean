-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_categories.monoidal_category
import ..discrete_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

definition CartesianProductOfCategories : MonoidalStructure CategoryOfCategoriesAndFunctors.{u v} := {
  tensor      := {
    onObjects     := λ p, ProductCategory p.1 p.2,
    onMorphisms   := λ _ _ p, ProductFunctor p.1 p.2,
    identities    := ♯,
    functoriality := ♮
  },
  tensor_unit := DiscreteCategory.{u v} punit,
  associator_transformation := {
    components := λ t, ProductCategoryAssociator t.1.1 t.1.2 t.2,
    naturality := ♮
  },
  left_unitor  := {
    components := λ p, RightProjection _ p,
    naturality := ♮
  },
  right_unitor := {
    components := λ p, LeftProjection p _,
    naturality := ♮
  },
  pentagon := ♯,
  triangle := ♮,
  associator_is_isomorphism   := {
    inverse := {
      components := λ t, ProductCategoryInverseAssociator t.1.1 t.1.2 t.2,
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  },
  left_unitor_is_isomorphism  := {
    inverse := {
      components := λ t, LeftInjectionAt punit.star t,
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  },
  right_unitor_is_isomorphism := {
    inverse := {
      components := λ t, RightInjectionAt punit.star t,
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  }
}

-- PROJECT it's symmetric

end tqft.categories.monoidal_category