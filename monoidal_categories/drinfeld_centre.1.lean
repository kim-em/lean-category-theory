-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .drinfeld_centre

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category

namespace tqft.categories.drinfeld_centre

local attribute [reducible] lift_t coe_t coe_b
local attribute [ematch] MonoidalCategory.interchange_right_identity  MonoidalCategory.interchange_left_identity

definition DrinfeldCentreAsMonoidalCategory ( C : MonoidalCategory ) : MonoidalCategory := {
  DrinfeldCentreAsCategory C with
  tensor_unit := {
    object := C^.tensor_unit,
    commutor := {
      morphism  := {
        components := λ X, C^.compose (C^.left_unitor X) (C^.right_unitor_is_isomorphism^.inverse X),
        naturality := sorry
      },
      inverse   := {
        components := λ X, C^.compose (C^.right_unitor X) (C^.left_unitor_is_isomorphism^.inverse X),
        naturality := sorry
      },
      witness_1 := sorry,
      witness_2 := sorry
    }
  },
  tensor := {
    onObjects   := λ p, {
      object   := C^.tensor (p.1^.object, p.2^.object),
      commutor := {
        morphism := {
          components := λ X,
            C^.compose (C^.compose (C^.compose (C^.compose (
              C^.associator p.1^.object p.2^.object X
            ) (
              C^.tensorMorphisms (C^.identity p.1^.object) (p.2^.commutor^.morphism X)
            )) (
              C^.inverse_associator p.1^.object X p.2^.object
            )) (
              C^.tensorMorphisms (p.1^.commutor^.morphism X) (C^.identity p.2^.object)
            )) (
              C^.associator X p.1^.object p.2^.object
            ),
          naturality := sorry
        },
        inverse := {
          components := sorry,
          naturality := sorry
        },
        witness_1 := sorry,
        witness_2 := sorry
      }
    },
    onMorphisms := sorry,
    identities := sorry,
    functoriality := sorry
  },
  associator_transformation := {
    components := λ t, ⟨ C^.associator_transformation ((t.1.1^.object, t.1.2^.object), t.2^.object), ♮ ⟩,
    naturality := ♮
  },
  associator_is_isomorphism := sorry,
  left_unitor  := {
    components := λ X, ⟨ C^.left_unitor X^.object, ♮ ⟩,
    naturality := ♮
  },
  right_unitor  := {
    components := λ X, ⟨ C^.right_unitor X^.object, ♮ ⟩,
    naturality := ♮
  },
  left_unitor_is_isomorphism  := sorry,
  right_unitor_is_isomorphism := sorry,
  pentagon := ♮,
  triangle := ♮
}

-- PROJECT Drinfeld centre as a braided category.

end tqft.categories.drinfeld_centre
