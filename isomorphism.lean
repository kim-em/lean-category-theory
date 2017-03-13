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

structure is_isomorphism { C : Category } { X Y : C^.Obj } ( morphism : C X Y ) :=
  (inverse : C Y X)
  (witness_1 : C^.compose morphism inverse = C^.identity X)
  (witness_2 : C^.compose inverse morphism = C^.identity Y)

end tqft.categories.isomorphism
