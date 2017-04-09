-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .comparisons


open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.equivalence
open tqft.categories.examples.types
open tqft.categories.universal

namespace tqft.categories.universal

definition ConeCategories_agree { J C : Category } ( F : Functor J C ) : Equivalence (comma.Cones F) (Cones F) := {
  functor := comma_Cones_to_Cones F,
  inverse := Cones_to_comma_Cones F,
  isomorphism_1 := {
    morphism  := {
      components := λ cone, ⟨ begin unfold_unfoldable, unfold_unfoldable, dsimp, split, exact (C.identity cone.fst), split, split, unfold Cone_to_comma_Cone._aux_1, dsimp, end, _ ⟩,
      naturality := ♯
    },
    inverse   := {
      components := λ cone, begin unfold_unfoldable, split,  end,
      naturality := ♯
    },
    witness_1 := sorry,
    witness_2 := sorry
  },
  isomorphism_2 := {
    morphism  := sorry,
    inverse   := sorry,
    witness_1 := sorry,
    witness_2 := sorry
  }
}

end tqft.categories.universal