-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

open tqft.categories

namespace tqft.categories.isomorphism

structure Isomorphism ( C: Category ) ( X Y : C^.Obj ) :=
  (morphism : C X Y)
  (inverse : C Y X)
  (witness_1 : C^.compose morphism inverse = C^.identity X)
  (witness_2 : C^.compose inverse morphism = C^.identity Y)

instance Isomorphism_coercion_to_morphism { C : Category } { X Y : C^.Obj } : has_coe (Isomorphism C X Y) (C X Y) :=
  { coe := Isomorphism.morphism }

definition Isomorphism.inverse_Isomorphism { C : Category } { X Y : C^.Obj } ( I : Isomorphism C X Y ) : Isomorphism C Y X :=
  {
    morphism  := I^.inverse,
    inverse   := I^.morphism,
    witness_1 := I^.witness_2,
    witness_2 := I^.witness_1
  }

structure is_Isomorphism { C : Category } { X Y : C^.Obj } ( morphism : C X Y ) :=
  (inverse : C Y X)
  (witness_1 : C^.compose morphism inverse = C^.identity X)
  (witness_2 : C^.compose inverse morphism = C^.identity Y)

instance is_Isomorphism_coercion_to_morphism { C : Category } { X Y : C^.Obj } ( f : C X Y ): has_coe (is_Isomorphism f) (C X Y) :=
  { coe := λ _, f }

structure Inverse { C: Category } { X Y : C^.Obj } ( morphism: C X Y ) :=
  (inverse : C Y X)
  (witness_1 : C^.compose morphism inverse = C^.identity X)
  (witness_2 : C^.compose inverse morphism = C^.identity Y)

end tqft.categories.isomorphism
