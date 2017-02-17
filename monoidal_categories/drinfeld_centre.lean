-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .braided_monoidal_category

--set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category

namespace tqft.categories.drinfeld_centre

structure HalfBraiding ( C : MonoidalCategory ) :=
    (object        : C^.Obj)
    (commutor: NaturalIsomorphism (tensor_on_left object) (tensor_on_right object))

instance HalfBraiding_coercion_to_object { C : MonoidalCategory } : has_coe (HalfBraiding C) (C^.Obj) :=
  { coe := HalfBraiding.object }

structure HalfBraidingMorphism { C : MonoidalCategory } ( X Y : HalfBraiding C ) :=
  (morphism : C^.Hom X Y)
  -- Probably there is a better way to express this condition!
  (witness : ∀ Z : C^.Obj, C^.compose (X^.commutor Z) (C^.tensorMorphisms (C^.identity Z) morphism) = C^.compose (C^.tensorMorphisms morphism (C^.identity Z)) (Y^.commutor Z))

-- --TODO: remove, not actually used
-- instance HalfBraidingMorphism_coercion_to_morphism { C : MonoidalCategory } ( X Y : HalfBraiding C ): has_coe (HalfBraidingMorphism  X Y) (C^.Hom X Y) :=
--   { coe := HalfBraidingMorphism.morphism }

-- TODO: most of the proofs don't work here. Hopefully after I learn to rewrite automatically this will work better.
-- definition DrinfeldCentreAsCategory ( C : MonoidalCategory ) : Category := {
--   Obj := HalfBraiding C,
--   Hom := λ X Y, HalfBraidingMorphism X Y,
--   identity := λ X, {
--     morphism := C^.identity X,
--     witness  := ♮
--   },
--   compose := λ _ _ _ f g, {
--     morphism := C^.compose f^.morphism g^.morphism,
--     witness  := ♮
--   },
--   left_identity  := ♮,
--   right_identity := ♮,
--   associativity  := ♮
-- }

end tqft.categories.drinfeld_centre
