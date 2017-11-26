-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..natural_isomorphism
import ..opposites
import ..products
import ..isomorphism
import ..types

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.isomorphism
open categories.types

namespace categories.adjunctions

definition HomAdjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  NaturalIsomorphism
    (FunctorComposition (OppositeFunctor L × IdentityFunctor D) (HomPairing D))
    (FunctorComposition (IdentityFunctor (Opposite C) × R) (HomPairing C))

definition mate { C D : Category } { L : Functor C D } { R : Functor D C } ( A : HomAdjunction L R ) { X : C.Obj } { Y : D.Obj } ( f : D.Hom (L.onObjects X) Y ) : C.Hom X (R.onObjects Y)
  := (A.morphism).components (X, Y) f

-- PROJECT lemmas about mates.

-- PROJECT -- to do this, we need to first define whiskering of NaturalIsomorphisms
-- See Remark 2.1.11 of Leinster
-- definition composition_of_HomAdjunctions
--   { C D E : Category } { L : Functor C D } { L' : Functor D E } { R : Functor D C } { R' : Functor E D }
--   ( A : HomAdjunction L R ) ( B : HomAdjunction L' R' )
--     : HomAdjunction (FunctorComposition L L') (FunctorComposition R' R) := sorry

end categories.adjunctions