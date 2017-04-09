-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...monoidal_categories.monoidal_category
import ...monoidal_categories.braided_monoidal_category
import .types

namespace tqft.categories.examples.types

open tqft.categories
open tqft.categories.monoidal_category
open tqft.categories.braided_monoidal_category

-- PROJECT really this should be a special case of the (uniquely braided, symmetric) monoidal structure coming from a product.

@[unfoldable] definition TensorProductOfTypes : TensorProduct CategoryOfTypes :=
{
  onObjects     := λ p, p.1 × p.2,
  onMorphisms   := λ _ _ p q, (p.1 q.1, p.2 q.2),
  identities    := ♯,
  functoriality := ♮
}

-- PROJECT it would be great to generate all these _is_isomorphism fields via refine
@[unfoldable] definition MonoidalCategoryOfTypes : MonoidalStructure CategoryOfTypes :=
{
  tensor      := TensorProductOfTypes,
  tensor_unit := punit,
  associator_transformation := {
    morphism := {
      components := λ p t, (t.1.1, (t.1.2, t.2)),
      naturality := ♮
    },
    inverse := {
      components := λ p t, ((t.1, t.2.1), t.2.2),
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  },
  left_unitor := {
    morphism := {
      components := λ p t, t.2,
      naturality := ♮
    },
    inverse := {
      components := λ p t, (punit.star, t),
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♮
  },
  right_unitor := {
    morphism := {
      components := λ p t, t.1,
      naturality := ♮
    },
    inverse := {
      components := λ p t, (t, punit.star),
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♮
  },
  pentagon := ♯,
  triangle := ♯
}

@[unfoldable] definition SymmetricMonoidalCategoryOfTypes : Symmetry MonoidalCategoryOfTypes := {
  braiding := {
   morphism  := {
     components := λ p t, (t.snd, t.fst),
     naturality := ♮
   },
   inverse   := {
     components := λ p t, (t.snd, t.fst),
     naturality := ♮
   },
   witness_1 := ♯,
   witness_2 := ♯ 
  },
  hexagon_1 := ♯,
  hexagon_2 := ♯,
  symmetry  := ♯
}

end tqft.categories.examples.types
