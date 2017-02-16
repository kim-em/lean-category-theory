-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .category
import .functor
import .natural_transformation
import .products
import .monoidal_category

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

definition left_parenthesised
  { C : MonoidalCategory } 
  { X : C^.Obj } 
  ( multiplication : C^.Hom (C^.tensor (X, X)) X ) : C^.Hom (C^.tensorObjects (C^.tensorObjects X X) X) X := 
    C^.compose (C^.tensorMorphisms multiplication (C^.identity X)) multiplication

definition right_parenthesised
  { C : MonoidalCategory } 
  { X : C^.Obj } 
  ( multiplication : C^.Hom (C^.tensor (X, X)) X ) : C^.Hom (C^.tensorObjects (C^.tensorObjects X X) X) X := 
    C^.compose (C^.associator X X X) (C^.compose (C^.tensorMorphisms (C^.identity X) multiplication) multiplication)

structure SemigroupObject ( C : MonoidalCategory ) :=
  ( object         : C^.Obj )
  ( multiplication : C^.Hom (C^.tensor (object, object)) object)
  ( associativity  : left_parenthesised multiplication = right_parenthesised multiplication )

end tqft.categories.internal_objects