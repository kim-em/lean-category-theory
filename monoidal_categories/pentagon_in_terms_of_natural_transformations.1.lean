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

local attribute [reducible] lift_t coe_t coe_b

lemma pentagon_in_terms_of_natural_transformations
  ( C : MonoidalCategory ) :
  pentagon_2step C = pentagon_3step C :=
  begin
    blast, -- This just unfolds definitions and introduces variables
    induction X with PQR S,
    induction PQR with PQ R,
    induction PQ with P Q,
    pose p := C^.pentagon P Q R S,
    blast, -- this simplifies the hypothesis p back to something reasonable
    repeat { rewrite Functor.identities C^.tensor }, -- we shouldn't have to do this, as Functor.identities has [simp]
    blast,                                           -- cleaning up mess...
    repeat { rewrite C^.right_identity },            -- again, we shouldn't need to do these, Category.left_identity has [simp] too
    repeat { rewrite C^.left_identity },
    exact p
  end

end tqft.categories.monoidal_category