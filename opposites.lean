-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .functor

open tqft.categories
open tqft.categories.functor

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

end tqft.categories