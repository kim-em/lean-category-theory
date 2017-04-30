-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .functor
import .products.products
import .examples.types.types

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.examples.types

namespace tqft.categories

definition Opposite ( C : Category ) : Category :=
{
    Obj := C.Obj,
    Hom := λ X Y, C.Hom Y X,
    compose  := λ _ _ _ f g, C.compose g f,
    identity := λ X, C.identity X,
    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

definition OppositeFunctor { C D : Category } ( F : Functor C D ) : Functor (Opposite C) (Opposite D) :=
{
  onObjects     := F.onObjects,
  onMorphisms   := λ X Y f, F.onMorphisms f,
  identities    := ♯,
  functoriality := ♯
}

definition { u v } HomPairing ( C : Category.{u v} ) : Functor ((Opposite C) × C) CategoryOfTypes.{v} :=
{
  onObjects     := λ p, C.Hom p.1 p.2,
  onMorphisms   := λ _ _ f, λ g, C.compose (C.compose f.1 g) f.2,
  identities    := ♯,
  functoriality := ♯
}

-- PROJECT opposites preserve products, functors, slices.

end tqft.categories