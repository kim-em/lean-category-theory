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
  (witness : ∀ Z : C^.Obj, C^.compose (X^.commutor Z) (C^.tensorMorphisms (C^.identity Z) morphism) = C^.compose (C^.tensorMorphisms morphism (C^.identity Z)) (Y^.commutor Z))

attribute [ematch] HalfBraidingMorphism.witness


@[pointwise] lemma HalfBraidingMorphism_equal
  { C : MonoidalCategory }
  { X Y : HalfBraiding C }
  { f g : HalfBraidingMorphism X Y }
  ( w : f^.morphism = g^.morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

local attribute [ematch] MonoidalCategory.interchange_right_identity  MonoidalCategory.interchange_left_identity

-- TODO understand why we can't just blast this; see below

@[ematch] lemma HalfBraidingMorphism.witness' { C : MonoidalCategory } { X Y : HalfBraiding C } ( f : HalfBraidingMorphism X Y ) ( Z : C^.Obj )
  : C^.compose (X^.commutor Z) (@Functor.onMorphisms _ _ C^.tensor (Z, _) (Z, _) (C^.identity Z, f^.morphism)) = C^.compose (@Functor.onMorphisms _ _ C^.tensor (_, Z) (_, Z) (f^.morphism, C^.identity Z)) (Y^.commutor Z)
  := begin
       rewrite f^.witness
     end
@[ematch] lemma HalfBraidingMorphism.witness'' { C : MonoidalCategory } { X Y : HalfBraiding C } ( f : HalfBraidingMorphism X Y ) ( Z : C^.Obj )
  : C^.compose (X^.commutor^.morphism^.components Z) (@Functor.onMorphisms _ _ C^.tensor (Z, _) (Z, _) (C^.identity Z, f^.morphism)) = C^.compose (@Functor.onMorphisms _ _ C^.tensor (_, Z) (_, Z) (f^.morphism, C^.identity Z)) (Y^.commutor^.morphism^.components Z)
  := begin
       rewrite f^.witness
     end
#check HalfBraidingMorphism.witness''

definition DrinfeldCentreAsCategory ( C : MonoidalCategory.{u v} ) : Category := {
  Obj := HalfBraiding C,
  Hom := λ X Y, HalfBraidingMorphism X Y,
  identity := λ X, {
    morphism := C^.identity X,
    witness  := ♮
  },
  compose := λ P Q R f g, {
    morphism := C^.compose f^.morphism g^.morphism,
    witness  :=
      begin
        intros, 
        dsimp,
        rewrite C^.interchange_right_identity,
        rewrite C^.interchange_left_identity,
        rewrite - C^.associativity,
        rewrite f^.witness,
        rewrite C^.associativity,
        -- blast, -- TODO I guess blast might not want to rewrite along witness, but surely witness'' is okay?
        rewrite HalfBraidingMorphism.witness'' g,
        -- rewrite g^.witness,
        rewrite C^.associativity
      end
  },
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

end tqft.categories.drinfeld_centre