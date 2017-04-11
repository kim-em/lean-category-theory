-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import .monoidal_structure_from_products

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category
open tqft.categories.universal

namespace tqft.categories.monoidal_category

-- definition MonoidalStructure_from_Products { C : Category } [ has_FiniteProducts C ] : MonoidalStructure C :=
-- {
--     tensor := TensorProduct_from_Products,
--     tensor_unit := terminal_object,
--     associator_transformation := Associator_for_Products,
--     left_unitor               := LeftUnitor_for_Products,
--     right_unitor              := RightUnitor_for_Products,
--     pentagon := sorry,
--     triangle := begin
--       dunfold_everything'
--      end
-- }

-- PROJECT show that this monoidal structure is uniquely braided
-- PROJECT and that braiding is symmetric

end tqft.categories.monoidal_category