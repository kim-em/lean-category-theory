-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .cartesian_product
import ...monoidal_categories.braided_monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.braided_monoidal_category

namespace tqft.categories.monoidal_category

definition SymmetryOnCartesianProductOfCategories : Symmetry CartesianProductOfCategories := {
  braiding             := {
    morphism  := {
      components := λ p, SwitchProductCategory p.1 p.2,
      naturality := ♮
    },
    inverse   := {
      components := λ p, SwitchProductCategory p.2 p.1,
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  },
  hexagon_1 := ♯,
  hexagon_2 := ♯,
  symmetry  := ♯
}

end tqft.categories.monoidal_category