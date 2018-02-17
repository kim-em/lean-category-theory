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

universes u u₁ u₂

structure Idempotent (C : Type u) [category C] :=
   (object : C)
   (idempotent : Hom object object)
   (witness : idempotent ≫ idempotent = idempotent . obviously)

make_lemma Idempotent.witness
attribute [simp,ematch] Idempotent.witness_lemma

local attribute [ematch] subtype.property

structure Idempotent_morphism {C : Type u} [category C] (X Y : Idempotent C) :=
(morphism : Hom X.object Y.object)
(left : X.idempotent ≫ morphism = morphism . obviously)
(right : morphism ≫ Y.idempotent = morphism . obviously)

make_lemma Idempotent_morphism.left
make_lemma Idempotent_morphism.right
attribute [simp,ematch] Idempotent_morphism.left_lemma Idempotent_morphism.right_lemma

@[applicable] lemma NaturalTransformations_componentwise_equal
  {C : Type u} [category C] (X Y : Idempotent C)
  (f g : Idempotent_morphism X Y)
  (w : f.morphism = g.morphism) : f = g :=
  begin
    induction f,
    induction g,
    tidy
  end


instance IdempotentCompletion (C : Type u) [category C]  : category (Idempotent C) := {
  Hom            := Idempotent_morphism,
  identity       := λ X, ⟨ X.idempotent ⟩,
  compose        := λ X Y Z f g, ⟨ f.morphism ≫ g.morphism ⟩
}

definition functor_to_IdempotentCompletion (C : Type u) [category C] : Functor C (Idempotent C) := {
  onObjects     := λ X, ⟨ X, 𝟙 X ⟩,
  onMorphisms   := λ _ _ f, ⟨ f, ♮ ⟩
}

-- -- PROJECT
-- definition IdempotentCompletion_functorial (C : Type u) [category C] (D : Type u) [category D] : Functor (Functor C D) (Functor (Idempotent C) (Idempotent D)) := {

open categories.equivalence

-- lemma embedding_in_IdempotentCompletition (C : Type u) [category C]  : Embedding (functor_to_IdempotentCompletion C) :=
-- begin
--   unfold Embedding,
--   split,
--   begin 
--     tidy {trace_result:=tt}, 
--     exact f_val,
--     refl, -- TODO Goals says 'f_val = f_val', but is secretly still '?m_1[C, X, Y, f_1, _] = f_1',
--     -- I posted a gist about this, and ask Mario about it: https://gist.github.com/semorrison/ddee284b92d64c931a21b5853cf6f1e1
--     -- sorry, 
--   end,
--   begin
--     tidy,
--   end
-- end

variable {C : Type u₁}
variable [category C]
variable {D : Type u₂}
variable [category D]

definition restrict_Functor_from_IdempotentCompletion (F : Functor (Idempotent C) D) : Functor C D :=
  FunctorComposition (functor_to_IdempotentCompletion C) F

@[simp] private lemma double_idempotent_morphism_left (X Y : Idempotent (Idempotent C))
(f : Hom X Y)
: (X.idempotent).morphism ≫ (f.morphism).morphism = (f.morphism).morphism :=
congr_arg Idempotent_morphism.morphism f.left
@[simp] private lemma double_idempotent_morphism_right (X Y : Idempotent (Idempotent C))
(f : Hom X Y)
:(f.morphism).morphism ≫ (Y.idempotent).morphism = (f.morphism).morphism :=
congr_arg Idempotent_morphism.morphism f.right

private def IdempotentCompletion_idempotent_functor (C : Type u) [category C] : Functor (Idempotent (Idempotent C)) (Idempotent C) :=
{
    onObjects     := λ X, ⟨ X.object.object, X.idempotent.morphism, congr_arg Idempotent_morphism.morphism X.witness ⟩, -- PROJECT think about automation here
    onMorphisms   := λ X Y f, ⟨ f.morphism.morphism, ♯ ⟩
}
private def IdempotentCompletion_idempotent_inverse (C : Type u) [category C] : Functor (Idempotent C) (Idempotent (Idempotent C)) :=
{
    onObjects     := λ X, ⟨ X, ⟨ X.idempotent, ♮ ⟩, ♯ ⟩,
    onMorphisms   := λ X Y f, ⟨ f, ♯ ⟩
}

-- PROJECT prove these lemmas about idempotent completion

-- lemma IdempotentCompletion_idempotent (C : Type u) [category C] :
--   Equivalence (IdempotentCompletion (IdempotentCompletion C)) (IdempotentCompletion C) :=
-- {
--   functor := IdempotentCompletion_idempotent_functor C,
--   inverse := IdempotentCompletion_idempotent_inverse C,
--   isomorphism_1 := begin tidy, exact C.identity _, tidy, induction f_2, tidy, end, -- PROJECT very slow??
--   isomorphism_2 := sorry
--}

-- Oh, I guess I had originally intended that this should use the previous results... oh well.
definition extend_Functor_to_IdempotentCompletion (F : Functor C (Idempotent D)) : 
  Functor (Idempotent C) (Idempotent D) :=
{
  onObjects     := λ X, let FX := F.onObjects X.object in
                         ⟨ FX.object, 
                           (F.onMorphisms X.idempotent).morphism, 
                           begin 
                             have p := F.functoriality X.idempotent X.idempotent, 
                             have p' := congr_arg Idempotent_morphism.morphism p, 
                             tidy, 
                           end
                         ⟩,
  onMorphisms   := λ X Y f, ⟨ (F.onMorphisms f.morphism).morphism, 
                              begin 
                                -- tidy, 
                                have p := F.functoriality X.idempotent f.morphism, 
                                have p' := congr_arg Idempotent_morphism.morphism p, 
                                rewrite f.left_lemma at p', 
                                exact eq.symm p', 
                              end,
                              begin
                                -- tidy, 
                                have p := F.functoriality f.morphism Y.idempotent, 
                                have p' := congr_arg Idempotent_morphism.morphism p, 
                                rewrite f.right_lemma at p', 
                                exact eq.symm p',
                              end ⟩
}

-- lemma Functor_from_IdempotentCompletion_determined_by_restriction 
--   {C D : Category} (F : Functor (IdempotentCompletion C) (IdempotentCompletion D)) :
--     NaturalIsomorphism (extend_Functor_to_IdempotentCompletion (restrict_Functor_from_IdempotentCompletion F)) F := 
--       sorry

-- PROJECT idempotent completion left adjoint to the forgetful functor from categories to semicategories?

end categories.idempotent_completion
