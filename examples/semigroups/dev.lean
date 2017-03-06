-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category_of_semigroups

namespace tqft.categories.examples.semigroups

open tqft.categories.braided_monoidal_category
open tqft.categories.examples.semigroups

universe variables u

-- definition SymmetricMonoidalCategoryOfSemigroups : SymmetricMonoidalCategory := {
--   BraidedMonoidalCategoryOfSemigroups.{u} with
--   symmetry := begin
--                 blast,
--                 dsimp [ BraidedMonoidalCategoryOfSemigroups ],
--                 blast,
--                 dsimp [ MonoidalCategoryOfSemigroups ],
--                 exact sorry
--               end
-- }

end  tqft.categories.examples.semigroups