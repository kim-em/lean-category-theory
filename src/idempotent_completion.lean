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
   ( object : C.Obj )
   ( idempotent : C.Hom object object )
   ( witness : C.compose idempotent idempotent = idempotent )

attribute [simp,ematch] Idempotent.witness

local attribute [ematch] subtype.property

definition IdempotentCompletion ( C: Category ) : Category :=
{
  Obj            := Idempotent C,
  Hom            := λ X Y, { f : C.Hom X.object Y.object // C.compose X.idempotent f = f ∧ C.compose f Y.idempotent = f },
  identity       := λ X, ⟨ X.idempotent, ♮ ⟩,
  compose        := λ X Y Z f g, ⟨ C.compose f.val g.val, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♮
}

definition functor_to_IdempotentCompletion ( C : Category ) : Functor C (IdempotentCompletion C) := {
  onObjects     := λ X, ⟨ X, C.identity X, ♮ ⟩,
  onMorphisms   := λ _ _ f, ⟨ f, ♮ ⟩,
  identities    := ♮,
  functoriality := ♮
}

-- open tqft.categories.equivalence

@[simp] lemma subtype.first { α : Type } { P : α → Prop } { X Y : α } { hX : P X} { hY : P Y } : (subtype.mk X hX  = subtype.mk Y hY) ↔ (X = Y) := begin
  split,
  {
    intros,
    exact congr_arg subtype.val a,
  },
  {
    intros,
    blast
  }
end

-- PROJECT show the embedding really was full and faithful
-- lemma embedding_in_IdempotentCompletition ( C: Category ) : Embedding (functor_to_IdempotentCompletion C) :=
-- begin
--   unfold Embedding,
--   split,
--   begin 
--     -- TODO blast should just do this, if not for the tactic.change problem.
--     unfold Full,
--     unfold Surjective,
--     unfold functor_to_IdempotentCompletion,
--     intros,
--     split,
--     dsimp, -- FIXME tactic.change error: https://github.com/leanprover/lean/issues/1503
--     unfold functor_to_IdempotentCompletion._aux_2,
--     dsimp,
--     fsplit,
--     unfold IdempotentCompletion,
--     dsimp,
--     intros f,
--     exact f.val,  
--     apply funext,
--     intros,  
--     simp
--   end,
--   begin
--     blast, -- This should finish it off. How do we get subtype.first, above, to do its job?
--     exact congr_arg subtype.val a
--   end
-- end

-- definition restrict_Functor_from_IdempotentCompletion { C D : Category } ( F : Functor (IdempotentCompletion C) D ) : Functor C D :=
--   FunctorComposition (functor_to_IdempotentCompletion C) F

-- PROJECT prove these lemmas about idempotent completion

-- lemma IdempotentCompletion_idempotent ( C : Category ) :
--   Equivalence (IdempotentCompletion (IdempotentCompletion C)) (IdempotentCompletion C) :=
-- {
--   functor := {
--     onObjects     := λ X, ⟨ X.object.object, X.idempotent.val, ♮ ⟩,
--     onMorphisms   := λ X Y f, ⟨ f.val.val, begin blast, exact congr_arg subtype.val f.property.left end ⟩,
--     identities    := ♮,
--     functoriality := ♮
--   },
--   inverse := {
--     onObjects     := λ X, ⟨ X, ⟨ X.idempotent, ♮ ⟩, ♯ ⟩,
--     onMorphisms   := λ X Y f, ⟨ f, ♯ ⟩,
--     identities    := ♮,
--     functoriality := ♮
--   },
--   isomorphism_1 := begin
--                      blast,
--                      admit
--                    end,
--   isomorphism_2 := sorry
-- }

-- definition extend_Functor_to_IdempotentCompletion { C D : Category } ( F : Functor C (IdempotentCompletion D) ) : 
--   Functor (IdempotentCompletion C) (IdempotentCompletion D) := 
--     sorry

-- lemma Functor_from_IdempotentCompletion_determined_by_restriction 
--   { C D : Category } ( F : Functor (IdempotentCompletion C) (IdempotentCompletion D) ) :
--     NaturalIsomorphism (extend_Functor_to_IdempotentCompletion (restrict_Functor_from_IdempotentCompletion F)) F := 
--       sorry

-- PROJECT idempotent completion left adjoint to the forgetful functor from categories to semicategories?

end tqft.categories.idempotent_completion
