-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .semigroups

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

structure MonoidObject { C : Category } ( m : MonoidalStructure C ) extends SemigroupObject m := 
  ( unit : C.Hom m.tensor_unit object )
  -- TODO why is components needed here
  -- ( left_identity  : C.compose (m.left_unitor_is_isomorphism.inverse.components object) (C.compose (m.tensorMorphisms unit (C.identity object)) multiplication) = C.identity object )
  -- ( right_identity : C.compose (m.right_unitor_is_isomorphism.inverse.components object) (C.compose (m.tensorMorphisms (C.identity object) unit) multiplication) = C.identity object )
  ( left_identity  : C.compose (m.tensorMorphisms unit (C.identity object)) multiplication = C.compose (m.left_unitor object) (C.identity object) )
  ( right_identity : C.compose (m.tensorMorphisms (C.identity object) unit) multiplication = C.compose (m.right_unitor object) (C.identity object) )

attribute [simp,ematch] MonoidObject.left_identity
attribute [simp,ematch] MonoidObject.right_identity

-- instance MonoidObject_coercion_to_SemigroupObject { C : MonoidalCategory } : has_coe (MonoidObject C) (SemigroupObject C) :=
--   { coe := MonoidObject.to_SemigroupObject }

end tqft.categories.internal_objects