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

attribute [simp] MonoidalCategory.left_identity
attribute [simp] MonoidalCategory.right_identity

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
    repeat { rewrite C^.tensor^.identities }, -- we shouldn't have to do this, as Functor.identities has [simp]
    blast
  end

end tqft.categories.monoidal_category
