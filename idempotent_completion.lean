-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

open tqft.categories

namespace tqft.categories.idempotent_completion

structure Idempotent ( C : Category ) :=
   ( obj : C^.Obj )
   ( idempotent : C obj obj )
   ( witness : C^.compose idempotent idempotent = idempotent )

attribute [simp,ematch] Idempotent.witness

local attribute [ematch] subtype.property

definition IdempotentCompletion ( C: Category ) : Category :=
{
  Obj            := Idempotent C,
  Hom            := λ X Y, { f : C X^.obj Y^.obj // C^.compose X^.idempotent f = f ∧ C^.compose f Y^.idempotent = f },
  identity       := λ X, ⟨ X^.idempotent, ♮ ⟩,
  compose        := λ X Y Z f g, ⟨ C^.compose f^.val g^.val, ♮ ⟩,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

end tqft.categories.idempotent_completion
