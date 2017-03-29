-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_category

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

structure SemigroupObject { C : Category } ( m : MonoidalStructure C ) :=
  ( object         : C^.Obj )
  ( multiplication : C^.Hom (m^.tensor (object, object)) object)
  ( associativity  : C^.compose (m^.tensorMorphisms multiplication (C^.identity object)) multiplication = C^.compose (m^.associator object object object) (C^.compose (m^.tensorMorphisms (C^.identity object) multiplication) multiplication) )

attribute [ematch] SemigroupObject.associativity

instance SemigroupObject_coercion_to_object { C : Category } { m : MonoidalStructure C } : has_coe (SemigroupObject m) (C^.Obj) :=
  { coe := SemigroupObject.object }

end tqft.categories.internal_objects