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

-- FIXME where do these lost meta-variables come from?
definition LeftUnitor_for_Products ( C : Category ) [ has_FiniteProducts C ] : LeftUnitor terminal_object (TensorProduct_from_Products C) :=
begin
  tidy, 
end

-- definition RightUnitor_for_Products ( C : Category ) [ has_FiniteProducts C ] : RightUnitor terminal_object (TensorProduct_from_Products C) :=
-- begin
--   tidy, 
-- end

-- definition MonoidalStructure_from_Products { C : Category } [ has_FiniteProducts C ] : MonoidalStructure C :=
-- {
--     tensor := TensorProduct_from_Products C,
--     tensor_unit := terminal_object,
--     associator_transformation := Associator_for_Products C,
--     left_unitor               := LeftUnitor_for_Products C,
--     right_unitor              := RightUnitor_for_Products C,
--     pentagon := ♯,
--     triangle := sorry
-- }

-- PROJECT show that this monoidal structure is uniquely braided
-- PROJECT and that braiding is symmetric

end tqft.categories.monoidal_category