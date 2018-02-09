-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .equivalence
import .functor

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.idempotent_completion

structure Idempotent (C : Category) :=
   (object : C.Obj)
   (idempotent : C.Hom object object)
   (witness : C.compose idempotent idempotent = idempotent)

attribute [simp,ematch] Idempotent.witness

local attribute [ematch] subtype.property

definition IdempotentCompletion (C: Category) : Category :=
{
  Obj            := Idempotent C,
  Hom            := λ X Y, {f : C.Hom X.object Y.object // C.compose X.idempotent f = f ∧ C.compose f Y.idempotent = f},
  identity       := λ X, ⟨ X.idempotent, ♮ ⟩,
  compose        := λ X Y Z f g, ⟨ C.compose f.val g.val, ♮ ⟩
}

definition functor_to_IdempotentCompletion (C : Category) : Functor C (IdempotentCompletion C) := {
  onObjects     := λ X, ⟨ X, C.identity X, ♮ ⟩,
  onMorphisms   := λ _ _ f, ⟨ f, ♮ ⟩
}

-- -- PROJECT
-- definition IdempotentCompletion_functorial (C D : Category) : Functor (FunctorCategory C D) (FunctorCategory (IdempotentCompletion C) (IdempotentCompletion D)) := {
--   onObjects     := λ F, {
--     onObjects     := λ X, ⟨ F.onObjects X.object, F.onMorphisms X.idempotent, ♯ ⟩ ,
--     onMorphisms   := λ X Y f, ⟨ (F.onMorphisms f.val), ♯ ⟩,
--     identities    := ♯,
--     functoriality := ♯
--  },
--   onMorphisms   := λ F G τ, {
--     components := λ X, ⟨ τ.components X.object, 
--                          begin 
--                            tidy, 
--                           --  have p := τ.naturality,
--                            admit, admit
--                          end
--                        ⟩,
--     naturality := ♯
--  },
--   identities    := sorry, -- we've made a mistake somewhere..
--   functoriality := sorry
--}

open categories.equivalence

-- lemma embedding_in_IdempotentCompletition (C: Category) : Embedding (functor_to_IdempotentCompletion C) :=
-- begin
--   unfold Embedding,
--   split,
--   begin 
--     tidy {trace_result:=tt}, 
--     exact f_val,
--     refl, -- TODO Goals says 'f_val = f_val', but is secretly still '?m_1[C, X, Y, f_1, _] = f_1',
--     -- I posted a gist about this, and ask Mario about it: https://gist.github.com/semorrison/ddee284b92d64c931a21b5853cf6f1e1
--     -- admit, 
--   end,
--   begin
--     tidy,
--   end
-- end

definition restrict_Functor_from_IdempotentCompletion {C D : Category} (F : Functor (IdempotentCompletion C) D) : Functor C D :=
  FunctorComposition (functor_to_IdempotentCompletion C) F

private def IdempotentCompletion_idempotent_functor (C : Category) : Functor (IdempotentCompletion (IdempotentCompletion C)) (IdempotentCompletion C) :=
{
    onObjects     := λ X, ⟨ X.object.object, X.idempotent.val, begin induction X, tidy end ⟩,
    onMorphisms   := λ X Y f, ⟨ f.val.val, ♯ ⟩
}
private def IdempotentCompletion_idempotent_inverse (C : Category) : Functor (IdempotentCompletion C) (IdempotentCompletion (IdempotentCompletion C)) :=
{
    onObjects     := λ X, ⟨ X, ⟨ X.idempotent, ♮ ⟩, ♯ ⟩,
    onMorphisms   := λ X Y f, ⟨ f, ♯ ⟩
}

-- PROJECT prove these lemmas about idempotent completion

-- lemma IdempotentCompletion_idempotent (C : Category) :
--   Equivalence (IdempotentCompletion (IdempotentCompletion C)) (IdempotentCompletion C) :=
-- {
--   functor := IdempotentCompletion_idempotent_functor C,
--   inverse := IdempotentCompletion_idempotent_inverse C,
--   isomorphism_1 := begin tidy, exact C.identity _, tidy, induction f_2, tidy, end, -- PROJECT very slow??
--   isomorphism_2 := sorry
--}

-- Oh, I guess I had originally intended that this should use the previous results... oh well.
definition extend_Functor_to_IdempotentCompletion {C D : Category} (F : Functor C (IdempotentCompletion D)) : 
  Functor (IdempotentCompletion C) (IdempotentCompletion D) :=
{
  onObjects     := λ X, let FX := F.onObjects X.object in
                         ⟨ FX.object, 
                           (F.onMorphisms X.idempotent).val, 
                           begin 
                             have p := F.functoriality X.idempotent X.idempotent, 
                             have p' := congr_arg subtype.val p, 
                             tidy, 
                           end
                         ⟩,
  onMorphisms   := λ X Y f, ⟨ (F.onMorphisms f.val).val, 
                              begin 
                                tidy, 
                                have p := F.functoriality X.idempotent f_val, 
                                have p' := congr_arg subtype.val p, 
                                rewrite f_property_left at p', 
                                exact eq.symm p', 
                                -- tidy, 
                                have p := F.functoriality f_val Y.idempotent, 
                                have p' := congr_arg subtype.val p, 
                                rewrite f_property_right at p', 
                                exact eq.symm p',
                              end ⟩
}

-- lemma Functor_from_IdempotentCompletion_determined_by_restriction 
--   {C D : Category} (F : Functor (IdempotentCompletion C) (IdempotentCompletion D)) :
--     NaturalIsomorphism (extend_Functor_to_IdempotentCompletion (restrict_Functor_from_IdempotentCompletion F)) F := 
--       sorry

-- PROJECT idempotent completion left adjoint to the forgetful functor from categories to semicategories?

end categories.idempotent_completion
