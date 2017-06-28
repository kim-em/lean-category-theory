-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..natural_transformation
import ..opposites
import ..products.products
import ..isomorphism
import ..types

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.isomorphism
open categories.types

namespace categories.adjunction

definition HomAdjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  NaturalIsomorphism
    (FunctorComposition (OppositeFunctor L × IdentityFunctor D) (HomPairing D))
    (FunctorComposition (IdentityFunctor (Opposite C) × R) (HomPairing C))


-- PROJECT examples
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end categories.adjunction