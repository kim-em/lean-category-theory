-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .pentagon_in_terms_of_natural_transformations_definitions

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

-- set_option pp.implicit true

-- TODO automation
lemma pentagon_in_terms_of_natural_transformations
   { C : Category.{u v} } ( m : MonoidalStructure C ) :
  pentagon_3step m = pentagon_2step m :=
  begin
    dsimp,
    apply NaturalTransformations_componentwise_equal,
    intros,
    unfold_unfoldable,
    unfold_unfoldable, -- FIXME
    dsimp,
    induction X with PQR S,
    induction PQR with PQ R,
    induction PQ with P Q,
    dsimp, 
    simp,
    erewrite C.right_identity, -- TODO why are these erewrites necessary? simp should just do it!
    erewrite C.right_identity,
    erewrite C.right_identity,
    erewrite C.right_identity,
    erewrite C.left_identity,
    erewrite C.left_identity,
    -- erewrite m.pentagon P Q R S, --- TODO This is pretty weird; Pentagon has λs in it.
    pose p := m.pentagon P Q R S,
    simp at p,
    dsimp at p,
    exact p
  end

end tqft.categories.monoidal_category
