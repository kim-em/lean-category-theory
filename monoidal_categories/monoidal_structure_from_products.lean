-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import .braided_monoidal_category
import ..universal.universal

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category
open tqft.categories.universal

namespace tqft.categories.monoidal_category

-- PROJECT

definition MonoidalStructure_from_Products { C : Category } ( products : has_FiniteProducts C ) : MonoidalStructure C :=
{
    tensor := {
        onObjects     := λ p, (products.binary_product p.1 p.2).product,
        onMorphisms   := λ X Y f, sorry,
        identities    := sorry,
        functoriality := sorry
    },
    tensor_unit := products.initial_object,
    associator_transformation := sorry,
    left_unitor               := sorry,
    right_unitor              := sorry,
    pentagon := sorry,
    triangle := sorry
}

-- PROJECT show that this monoidal structure is uniquely braided
-- PROJECT and that braiding is symmetric

end tqft.categories.monoidal_category