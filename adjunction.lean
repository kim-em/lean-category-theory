-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.adjunction



-- PROJECT, show these are a special case of a duality in a 2-category.

structure Adjunction ( C D : Category ) :=
  ( left_adjoint : Functor C D )
  ( right_adjoint : Functor D C )
  ( counit : NaturalTransformation (FunctorComposition left_adjoint right_adjoint) (IdentityFunctor C) )
  ( unit : NaturalTransformation (IdentityFunctor D) (FunctorComposition right_adjoint left_adjoint) )
  -- TODO triangles

end tqft.categories.adjunction