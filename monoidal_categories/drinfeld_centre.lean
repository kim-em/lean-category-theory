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

structure HalfBraiding { C : Category } ( m : MonoidalStructure C ) :=
    (object   : C^.Obj)
    (commutor : NaturalIsomorphism (m^.tensor_on_left object) (m^.tensor_on_right object))

instance HalfBraiding_coercion_to_object { C : Category } ( m : MonoidalStructure C ) : has_coe (HalfBraiding m) (C^.Obj) :=
  { coe := HalfBraiding.object }

structure HalfBraidingMorphism  { C : Category } { m : MonoidalStructure C } ( X Y : HalfBraiding m ) :=
  (morphism : C^.Hom X Y)
  (witness : ∀ Z : C^.Obj, C^.compose (X^.commutor Z) (m^.tensorMorphisms (C^.identity Z) morphism) = C^.compose (m^.tensorMorphisms morphism (C^.identity Z)) (Y^.commutor Z))

attribute [ematch] HalfBraidingMorphism.witness


@[pointwise] lemma HalfBraidingMorphism_equal
  { C : Category }
  { m : MonoidalStructure C }
  { X Y : HalfBraiding m }
  { f g : HalfBraidingMorphism X Y }
  ( w : f^.morphism = g^.morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

local attribute [ematch] MonoidalStructure.interchange_right_identity  MonoidalStructure.interchange_left_identity

-- FIXME automation!
definition DrinfeldCentre { C : Category } ( m : MonoidalStructure C )  : Category := {
  Obj := HalfBraiding m,
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
        rewrite m^.interchange_right_identity,
        rewrite m^.interchange_left_identity,
        rewrite - C^.associativity,
        rewrite f^.witness,
        rewrite C^.associativity,
        rewrite g^.witness,
        rewrite C^.associativity
      end
  },
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

end tqft.categories.drinfeld_centre