-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .pentagon_in_terms_of_natural_transformations_definitions

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

lemma pentagon_in_terms_of_natural_transformations
  ( C : MonoidalCategory ) :
  pentagon_3step C = pentagon_2step C :=
  begin
    blast,
    induction X with PQR S,
    induction PQR with PQ R,
    induction PQ with P Q,
    -- -- TODO ideally ematch would take care of this for us.
    pose p := C^.pentagon P Q R S,
    exact p
  end

end tqft.categories.monoidal_category
