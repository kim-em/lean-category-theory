-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .equivalence
import .functor

open categories
open categories.functor
open categories.natural_transformation

namespace categories.idempotent_completion

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

-- PROJECT
-- definition IdempotentCompletion_functorial ( C D : Category ) : Functor (FunctorCategory C D) (FunctorCategory (IdempotentCompletion C) (IdempotentCompletion D)) := {
--   onObjects     := λ F, {
--     onObjects     := λ X, ⟨ F.onObjects X.object, F.onMorphisms X.idempotent, ♯ ⟩ ,
--     onMorphisms   := λ X Y f, ⟨ (F.onMorphisms f.val), ♯ ⟩,
--     identities    := ♯,
--     functoriality := ♯
--   },
--   onMorphisms   := λ F G τ, {
--     components := λ X, ⟨ τ.components X.object, begin tidy, end ⟩,
--     naturality := ♯
--   },
--   identities    := ♯, -- we've made a mistake somewhere..
--   functoriality := sorry
-- }

open categories.equivalence

lemma embedding_in_IdempotentCompletition ( C: Category ) : Embedding (functor_to_IdempotentCompletion C) :=
begin
  unfold Embedding,
  split,
  begin 
    tidy,
    exact f_1,
    tidy,
  end,
  begin
    tidy, -- PROJECT This next step seems easily automatable.
    exact congr_arg subtype.val p
  end
end

definition restrict_Functor_from_IdempotentCompletion { C D : Category } ( F : Functor (IdempotentCompletion C) D ) : Functor C D :=
  FunctorComposition (functor_to_IdempotentCompletion C) F

-- PROJECT prove these lemmas about idempotent completion
-- lemma IdempotentCompletion_idempotent ( C : Category ) :
--   Equivalence (IdempotentCompletion (IdempotentCompletion C)) (IdempotentCompletion C) :=
-- {
--   functor := {
--     onObjects     := λ X, ⟨ X.object.object, X.idempotent.val, begin tidy, induction X, tidy, exact congr_arg subtype.val witness, end ⟩,
--     onMorphisms   := λ X Y f, ⟨ f.val.val, begin tidy, exact congr_arg subtype.val f_2.right, unfold_projections at f, have p := f.property.right, tidy, exact congr_arg subtype.val p, end ⟩,
--     identities    := ♮,
--     functoriality := ♮
--   },
--   inverse := {
--     onObjects     := λ X, ⟨ X, ⟨ X.idempotent, ♮ ⟩, ♯ ⟩,
--     onMorphisms   := λ X Y f, ⟨ f, begin tidy, exact f_2.right, tidy, exact f_2.left end ⟩,
--     identities    := ♮,
--     functoriality := ♮
--   },
--   isomorphism_1 := begin tidy, end, -- FIXME this gets stuck because we've improperly used identities automatically! -- how do we cancel attributes?
--   isomorphism_2 := sorry
-- }

-- Oh, I guess I had original intended that this should use the previous results... oh well.
definition extend_Functor_to_IdempotentCompletion { C D : Category } ( F : Functor C (IdempotentCompletion D) ) : 
  Functor (IdempotentCompletion C) (IdempotentCompletion D) :=
{
  onObjects     := λ X, let FX := F.onObjects X.object in
                         ⟨ FX.object, 
                           (F.onMorphisms X.idempotent).val, 
                           begin 
                             tidy, 
                             have p := F.functoriality X.idempotent X.idempotent, 
                             have p' := congr_arg subtype.val p, 
                             tidy, 
                            --  exact eq.symm p'
                           end
                         ⟩,
  onMorphisms   := λ X Y f, ⟨ (F.onMorphisms f.val).val, 
                              begin 
                                tidy, 
                                have p := F.functoriality X.idempotent f_1, 
                                have p' := congr_arg subtype.val p, 
                                rewrite f_2.right at p', 
                                exact eq.symm p', 
                                tidy, 
                                have p := F.functoriality f_1 Y.idempotent, 
                                have p' := congr_arg subtype.val p, 
                                rewrite f_2.left at p', 
                                exact eq.symm p',
                              end ⟩,
  identities    := ♯,
  functoriality := ♯, 
}

-- lemma Functor_from_IdempotentCompletion_determined_by_restriction 
--   { C D : Category } ( F : Functor (IdempotentCompletion C) (IdempotentCompletion D) ) :
--     NaturalIsomorphism (extend_Functor_to_IdempotentCompletion (restrict_Functor_from_IdempotentCompletion F)) F := 
--       sorry

-- PROJECT idempotent completion left adjoint to the forgetful functor from categories to semicategories?

end categories.idempotent_completion
