-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category

namespace tqft.categories.strict_monoidal_category

structure StrictMonoidalCategory extends parent: MonoidalCategory :=
  ( tensorAssociativeOnObjects : forall X Y Z : Obj, tensorObjects (tensorObjects X Y) Z = tensorObjects X (tensorObjects Y Z) )
  ( associatorTrivial : forall X Y Z : Obj, associator X Y Z = identity (tensorObject (tensorObjects X Y) Z) )

definition StrictTensorProduct

-- this ought to also return the equivalence
definition ListObjectsMonoidalCategory ( C : MonoidalCategory ) : MonoidalCategory := {
  Obj := list C^.Obj,
  Hom := \lambda X Y, C^.Hom sorry sorry,
  identity := \lambda X, sorry,
  compose := sorry,
  left_identity := sorry,
  right_identity := sorry,
  associativity := sorry
}

definition StrictTensorProduct ( C : MonoidalCategory ) : TensorProduct (ListObjectsMonoidalCategory C) := {
  onObjects := \lambda p, p._1 ++ p._2,
  onMorphisms := sorry,
  identities := sorry,
  functoriality := sorry
}

definition StrictifyMonoidalCategory ( C: MonoidalCategory ) : StrictMonoidalCategory := {
  ListObjectsMonoidalCategory C with
  tensor := StrictTensorProduct C,
  associator_transformation := sorry
}

end tqft.categories.strict_monoidal_category
