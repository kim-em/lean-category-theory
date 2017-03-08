-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..monoidal_categories.monoidal_category
import .types

namespace tqft.categories.examples.types

open tqft.categories
open tqft.categories.monoidal_category

definition TensorProductOfTypes : TensorProduct CategoryOfTypes :=
{
  onObjects     := λ p, p.1 × p.2,
  onMorphisms   := λ _ _ p q, (p.1 q.1, p.2 q.2),
  identities    := ♮,
  functoriality := ♮
}

-- I don't think this is a monoidal category if we don't assume
-- functional extensionality, though it is a lax monoidal
-- category. Otherwise there are too many endomorphisms of punit.
definition MonoidalCategoryOfTypes : MonoidalCategory :=
{
  CategoryOfTypes with
  tensor      := TensorProductOfTypes,
  tensor_unit := punit,
  associator_transformation := {
    components := λ p t, (t.1.1,(t.1.2, t.2)),
    naturality := ♮
  },
  -- left_unitor := {
  --   components := λ p t, t.2,
  --   naturality := ♮
  -- },
  -- right_unitor := {
  --   components := λ p t, t.1,
  --   naturality := ♮
  -- },

  associator_is_isomorphism := {
    inverse := {
      components := λ p t, ((t.1,t.2.1), t.2.2),
      naturality := ♮
    },
    witness_1 := sorry, -- ♮ causes a timeout here
    witness_2 := sorry  -- ♮ causes a timeout here
  },
  -- left_unitor_is_isomorphism := {
  --   inverse := {
  --     components := λ p t, (id, t),
  --     naturality := ♮
  --   },
  --   witness_1 := sorry,
  --   witness_2 := sorry
  -- },
  -- right_unitor_is_isomorphism := {
  --   inverse := {
  --     components := λ p t, (t, id),
  --     naturality := ♮
  --   },
  --   witness_1 := sorry,
  --   witness_2 := sorry
  -- },

  pentagon := ♮
  -- triangle := ♮
}

end tqft.categories.examples.types
