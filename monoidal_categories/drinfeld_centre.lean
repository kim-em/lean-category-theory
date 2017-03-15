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

structure HalfBraiding ( C : MonoidalCategory ) :=
    (object   : C^.Obj)
    (commutor : NaturalIsomorphism (tensor_on_left object) (tensor_on_right object))

instance HalfBraiding_coercion_to_object { C : MonoidalCategory } : has_coe (HalfBraiding C) (C^.Obj) :=
  { coe := HalfBraiding.object }

structure HalfBraidingMorphism { C : MonoidalCategory } ( X Y : HalfBraiding C ) :=
  (morphism : C^.Hom X Y)
  -- Probably there is a better way to express this condition!
  (witness : ∀ Z : C^.Obj, C^.compose (X^.commutor Z) (C^.tensorMorphisms (C^.identity Z) morphism) = C^.compose (C^.tensorMorphisms morphism (C^.identity Z)) (Y^.commutor Z))

-- --TODO: remove?, not actually used
-- instance HalfBraidingMorphism_coercion_to_morphism { C : MonoidalCategory } ( X Y : HalfBraiding C ): has_coe (HalfBraidingMorphism  X Y) (C^.Hom X Y) :=
--   { coe := HalfBraidingMorphism.morphism }

-- TODO: most of the proofs don't work here. Hopefully after I learn to rewrite automatically this will work better.
-- TODO: this takes way too long to compile
-- definition DrinfeldCentreAsCategory ( C : MonoidalCategory ) : Category := {
--   Obj := HalfBraiding C,
--   Hom := λ X Y, HalfBraidingMorphism X Y,
--   identity := λ X, {
--     morphism := C^.identity X,
--     witness  := begin
--                   blast,
--                   apply X^.commutor^.morphism^.naturality,
--                   exact sorry
--                 end
--   },
--   compose := λ P Q R f g, {
--     morphism := C^.compose f^.morphism g^.morphism,
--     witness  := begin
--                   blast,
--                   -- TODO similarly, I don't understand why this doesn't work
--                   rewrite MonoidalCategory.interchange_left_identity,
--                   exact sorry
--                 end
--   },
--   left_identity  := sorry,
--   right_identity := sorry,
--   associativity  := sorry
-- }

end tqft.categories.drinfeld_centre
