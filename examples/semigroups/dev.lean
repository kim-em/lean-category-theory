-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...monoidal_categories.braided_monoidal_category
import .monoidal_category_of_semigroups

open tqft.categories.natural_transformation
open tqft.categories.braided_monoidal_category

namespace tqft.categories.examples.semigroups

@[unfoldable] definition SymmetryOnCategoryOfSemigroups' : Symmetry MonoidalStructureOnCategoryOfSemigroups :=
begin
  refine {
    braiding             := {
      morphism  := {
        components := λ _, {
                            map := λ p, (p.2, p.1),
                            multiplicative := ♮
                          },
        naturality := ♮
      },
      inverse   := _,
      witness_1 := _,
      witness_2 := _
    },
    hexagon_1 := sorry,
    hexagon_2 := sorry,
    symmetry  := sorry
  },
  -- Everything below is an attempt to build the inverse in a way that automation could conceivably handle.
  unfold_unfoldable,
  split,
  intros X Y f,
  dsimp at X,
  induction X with X1 X2,
  induction X1 with X1α X1s,
  induction X2 with X2α X2s,
  dsimp at Y,
  induction Y with Y1 Y2,
  induction Y1 with Y1α Y1s,
  induction Y2 with Y2α Y2s,
  dsimp at f,
  induction f with f1 f2,
  simp,
  apply semigroup_morphism_pointwise_equality,
  intros x,
  dsimp at x,
  unfold TensorProduct_for_Semigroups at x,
  dsimp at x,
  induction x with x1 x2,
  dsimp,

end

end tqft.categories.examples.semigroups