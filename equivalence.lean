-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.equivalence

structure Equivalence ( C D : Category ) :=
  ( functor : Functor C D )
  ( inverse : Functor D C )
  ( isomorphism_1 : NaturalIsomorphism (FunctorComposition functor inverse) (IdentityFunctor C) )
  ( isomorphism_2 : NaturalIsomorphism (FunctorComposition inverse functor) (IdentityFunctor D) )

end tqft.categories.equivalence