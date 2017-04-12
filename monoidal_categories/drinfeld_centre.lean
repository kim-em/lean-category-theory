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

structure {u v} HalfBraiding { C : Category.{u v} } ( m : MonoidalStructure C ) :=
    (object   : C.Obj)
    (commutor : NaturalIsomorphism (m.tensor_on_left object) (m.tensor_on_right object))

definition {u v} HalfBraiding_coercion_to_object { C : Category.{u v} } ( m : MonoidalStructure C ) : has_coe (HalfBraiding m) (C.Obj) :=
  { coe := HalfBraiding.object }

attribute [instance] HalfBraiding_coercion_to_object

structure {u v} HalfBraidingMorphism  { C : Category.{u v} } { m : MonoidalStructure C } ( X Y : HalfBraiding m ) :=
  (morphism : C.Hom X Y)
  -- FIXME I've had to write out the statement gorily, so that it can match.
  -- (witness : ∀ Z : C.Obj, C.compose (X.commutor Z) (m.tensorMorphisms (C.identity Z) morphism) = C.compose (m.tensorMorphisms morphism (C.identity Z)) (Y.commutor Z))
  (witness : ∀ Z : C.Obj, C.compose (X.commutor.morphism.components Z) (@Functor.onMorphisms _ _ m.tensor (Z, X) (Z, Y) (C.identity Z, morphism)) = C.compose (@Functor.onMorphisms _ _ m.tensor (X, Z) (Y, Z) (morphism, C.identity Z)) (Y.commutor Z))

attribute [ematch] HalfBraidingMorphism.witness

@[pointwise] lemma HalfBraidingMorphism_equal
  { C : Category }
  { m : MonoidalStructure C }
  { X Y : HalfBraiding m }
  { f g : HalfBraidingMorphism X Y }
  ( w : f.morphism = g.morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

local attribute [ematch] MonoidalStructure.interchange_right_identity  MonoidalStructure.interchange_left_identity

-- set_option pp.implicit true
-- set_option pp.all true

local attribute [ematch] MonoidalStructure.interchange_right_identity
local attribute [ematch] MonoidalStructure.interchange_left_identity


definition {u v} DrinfeldCentre { C : Category.{u v} } ( m : MonoidalStructure C )  : Category := {
  Obj := HalfBraiding m,
  Hom := λ X Y, HalfBraidingMorphism X Y,
  identity := λ X, {
    morphism := C.identity X,
    witness  := ♯
  },
  compose := λ P Q R f g, {
    morphism := C.compose f.morphism g.morphism,
    witness  := 
      begin
        intros, 
        dsimp,
        rewrite m.interchange_right_identity,
        rewrite m.interchange_left_identity,
        erewrite - C.associativity,
        rewrite f.witness,
        rewrite C.associativity,
        -- blast,
        erewrite g.witness,
        -- blast, -- FIXME these blasts are unfolding too many implicit arguments.
                  -- https://github.com/leanprover/lean/issues/1509
        erewrite - C.associativity,
        trivial
      end
  },
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

end tqft.categories.drinfeld_centre