-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .braided_monoidal_category
import .tensor_with_object

--set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category

namespace tqft.categories.drinfeld_centre

universe variables u v

structure HalfBraiding ( C : MonoidalCategory ) :=
    (object   : C^.Obj)
    (commutor : NaturalIsomorphism (tensor_on_left object) (tensor_on_right object))

instance HalfBraiding_coercion_to_object { C : MonoidalCategory } : has_coe (HalfBraiding C) (C^.Obj) :=
  { coe := HalfBraiding.object }

structure HalfBraidingMorphism { C : MonoidalCategory } ( X Y : HalfBraiding C ) :=
  (morphism : C^.Hom X Y)
  -- Probably there is a better way to express this condition!
  (witness : ∀ Z : C^.Obj, C^.compose (X^.commutor Z) (C^.tensorMorphisms (C^.identity Z) morphism) = C^.compose (C^.tensorMorphisms morphism (C^.identity Z)) (Y^.commutor Z))

attribute [ematch] HalfBraidingMorphism.witness

local attribute [reducible] lift_t coe_t coe_b

definition DrinfeldCentreAsCategory ( C : MonoidalCategory.{u v} ) : Category := {
  Obj := HalfBraiding C,
  Hom := λ X Y, HalfBraidingMorphism X Y,
  identity := λ X, {
    morphism := C^.identity X,
    witness  := ♮
  },
  compose := λ P Q R f g, {
    morphism := C^.compose f^.morphism g^.morphism,
    witness  := sorry
  },
  left_identity  := sorry, -- TODO
  right_identity := sorry,
  associativity  := sorry
}

end tqft.categories.drinfeld_centre
