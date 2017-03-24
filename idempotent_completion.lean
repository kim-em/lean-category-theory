-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .equivalence
import .functor

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

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

definition embedding_in_IdempotentCompletion ( C : Category ) : Functor C (IdempotentCompletion C) := {
  onObjects     := λ X, ⟨ X, C^.identity X, ♮ ⟩,
  onMorphisms   := λ _ _ f, ⟨ f, ♮ ⟩,
  identities    := ♮,
  functoriality := ♮
}

-- PROJECT show the embedding really was full and faithful

definition restrict_Functor_from_IdempotentCompletion { C D : Category } ( F : Functor (IdempotentCompletion C) D ) : Functor C D :=
  FunctorComposition (embedding_in_IdempotentCompletion C) F

open tqft.categories.equivalence

-- PROJECT prove these lemmas about idempotent completion

-- lemma IdempotentCompletion_idempotent ( C : Category ) :
--   Equivalence (IdempotentCompletion (IdempotentCompletion C)) (IdempotentCompletion C) :=
--     sorry

-- definition extend_Functor_to_IdempotentCompletion { C D : Category } ( F : Functor C (IdempotentCompletion D) ) : 
--   Functor (IdempotentCompletion C) (IdempotentCompletion D) := 
--     sorry

-- lemma Functor_from_IdempotentCompletion_determined_by_restriction 
--   { C D : Category } ( F : Functor (IdempotentCompletion C) (IdempotentCompletion D) ) :
--     NaturalIsomorphism (extend_Functor_to_IdempotentCompletion (restrict_Functor_from_IdempotentCompletion F)) F := 
--       sorry

-- PROJECT idempotent completion left adjoint to the forgetful functor from categories to semicategories?

end tqft.categories.idempotent_completion
