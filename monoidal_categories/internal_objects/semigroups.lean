-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_category

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

structure SemigroupObject ( C : MonoidalCategory ) :=
  ( object         : C^.Obj )
  ( multiplication : C^.Hom (C^.tensor (object, object)) object)
  ( associativity  : C^.compose (C^.tensorMorphisms multiplication (C^.identity object)) multiplication = C^.compose (C^.associator object object object) (C^.compose (C^.tensorMorphisms (C^.identity object) multiplication) multiplication) )

attribute [ematch] SemigroupObject.associativity

instance SemigroupObject_coercion_to_object { C : MonoidalCategory } : has_coe (SemigroupObject C) (C^.Obj) :=
  { coe := SemigroupObject.object }

end tqft.categories.internal_objects