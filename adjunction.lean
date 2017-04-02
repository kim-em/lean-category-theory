-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.adjunction

@[reducible] definition Triangle_1
  { C D : Category }
  { L : Functor C D }
  { R : Functor D C }
  ( unit   : NaturalTransformation (IdentityFunctor D) (FunctorComposition R L) )
  ( counit : NaturalTransformation (FunctorComposition L R) (IdentityFunctor C) ) :=
  @vertical_composition_of_NaturalTransformations C D L (FunctorComposition (FunctorComposition L R) L) L ⟦ whisker_on_left L unit ⟧ ⟦ whisker_on_right counit L ⟧
  = IdentityNaturalTransformation L

@[reducible] definition Triangle_2
  { C D : Category }
  { L : Functor C D }
  { R : Functor D C }
  ( unit   : NaturalTransformation (IdentityFunctor D) (FunctorComposition R L) )
  ( counit : NaturalTransformation (FunctorComposition L R) (IdentityFunctor C) ) :=
  @vertical_composition_of_NaturalTransformations D C R (FunctorComposition (FunctorComposition R L) R) R ⟦ whisker_on_right unit R ⟧ ⟦ whisker_on_left R counit ⟧
  = IdentityNaturalTransformation R

structure Adjunction ( C D : Category ) :=
  ( left_adjoint  : Functor C D )
  ( right_adjoint : Functor D C )
  ( unit          : NaturalTransformation (IdentityFunctor D) (FunctorComposition right_adjoint left_adjoint) )
  ( counit        : NaturalTransformation (FunctorComposition left_adjoint right_adjoint) (IdentityFunctor C) )
  ( triangle_1    : Triangle_1 unit counit )
  ( triangle_2    : Triangle_2 unit counit )

-- PROJECT examples
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT hom-set adjunctions
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end tqft.categories.adjunction