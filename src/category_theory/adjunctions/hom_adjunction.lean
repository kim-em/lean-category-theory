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

end categories.adjunctions