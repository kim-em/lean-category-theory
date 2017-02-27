-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .pentagon_in_terms_of_natural_transformations

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

lemma pentagon_in_terms_of_natural_transformations
  ( C : MonoidalCategory ) :
  pentagon_2step C = pentagon_3step C :=
  begin
    blast,
    exact sorry
    -- begin[smt]
    --   eblast_using [ C^.pentagon ]
    -- end
  end

end tqft.categories.monoidal_category
