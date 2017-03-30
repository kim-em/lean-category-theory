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

local attribute [ematch] MonoidalStructure.interchange_right_identity  MonoidalStructure.interchange_left_identity

definition DrinfeldCentreTensorUnit { C : Category } ( m : MonoidalStructure C ) : (DrinfeldCentre m)^.Obj := {
    object := m^.tensor_unit,
    commutor := {
      morphism  := {
        components := λ X, C^.compose (m^.left_unitor X) (m^.right_unitor_is_isomorphism^.inverse^.components X),
        naturality := sorry
      },
      inverse   := {
        components := λ X, C^.compose (m^.right_unitor X) (m^.left_unitor_is_isomorphism^.inverse^.components X),
        naturality := sorry
      },
      witness_1 := sorry,
      witness_2 := sorry
    }
  }

-- definition DrinfeldCentreTensorProduct { C : Category } ( m : MonoidalStructure C ) : TensorProduct (DrinfeldCentre m) := {
--     onObjects   := λ p, {
--       object   := m^.tensor (p.1^.object, p.2^.object),
--       commutor := {
--         morphism := {
--           components := λ X,
--             C^.compose (C^.compose (C^.compose (C^.compose (
--               m^.associator p.1^.object p.2^.object X
--             ) (
--               m^.tensorMorphisms (C^.identity p.1^.object) (p.2^.commutor^.morphism^.components X)
--             )) (
--               m^.inverse_associator p.1^.object X p.2^.object
--             )) (
--               m^.tensorMorphisms (p.1^.commutor^.morphism^.components X) (C^.identity p.2^.object)
--             )) (
--               m^.associator X p.1^.object p.2^.object
--             ),
--           naturality := sorry
--         },
--         inverse := {
--           components := sorry,
--           naturality := sorry
--         },
--         witness_1 := sorry,
--         witness_2 := sorry
--       }
--     },
--     onMorphisms := sorry,
--     identities := sorry,
--     functoriality := sorry
--   }

-- definition DrinfeldCentreAssociator { C : Category } ( m : MonoidalStructure C ) : Associator (DrinfeldCentreTensorProduct m) := {
--     components := sorry, --λ t, ⟨ m^.associator_transformation ((t.1.1^.object, t.1.2^.object), t.2^.object), sorry ⟩,
--     naturality := sorry
--   }

-- definition DrinfeldCentreAsMonoidalCategory { C : Category } ( m : MonoidalStructure C ) : MonoidalStructure (DrinfeldCentre m) := {
--   tensor_unit := DrinfeldCentreTensorUnit m,
--   tensor := DrinfeldCentreTensorProduct m,
--   associator_transformation := DrinfeldCentreAssociator m,
--   associator_is_isomorphism := sorry,
--   left_unitor  := {
--     components := sorry, --λ X, ⟨ m^.left_unitor X^.object, sorry ⟩,
--     naturality := sorry
--   },
--   right_unitor  := {
--     components := sorry, --λ X, ⟨ m^.right_unitor X^.object, sorry ⟩,
--     naturality := sorry
--   },
--   left_unitor_is_isomorphism  := sorry,
--   right_unitor_is_isomorphism := sorry,
--   pentagon := sorry,
--   triangle := sorry
-- }

-- PROJECT Drinfeld centre as a braided category.

end tqft.categories.drinfeld_centre
