-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

open tqft.categories

namespace tqft.categories

@[unfoldable] definition Opposite ( C : Category ) : Category :=
{
    Obj := C.Obj,
    Hom := λ X Y, C.Hom Y X,
    compose  := λ _ _ _ f g, C.compose g f,
    identity := λ X, C.identity X,
    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

end tqft.categories