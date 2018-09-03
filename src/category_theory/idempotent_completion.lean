-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.equivalence

namespace category_theory

universes u u₁ u₂

structure Idempotent (C : Type (u+1)) [large_category C] :=
(object : C)
(idempotent : object ⟶ object)
(witness' : idempotent ≫ idempotent = idempotent . obviously)

restate_axiom Idempotent.witness'
attribute [simp,search] Idempotent.witness

local attribute [search] subtype.property

variables {C : Type (u+1)} [large_category C]

namespace Idempotent

structure morphism (X Y : Idempotent C) :=
(morphism : X.object ⟶ Y.object)
(left' : X.idempotent ≫ morphism = morphism . obviously)
(right' : morphism ≫ Y.idempotent = morphism . obviously)

restate_axiom morphism.left'
restate_axiom morphism.right'
attribute [simp,search] morphism.left morphism.right

@[extensionality] lemma ext {X Y : Idempotent C} (f g : morphism X Y) (w : f.morphism = g.morphism) : f = g :=
begin
  induction f,
  induction g,
  tidy
end

end Idempotent

instance IdempotentCompletion : large_category (Idempotent C) := 
{ hom  := Idempotent.morphism,
  id   := λ X, ⟨ X.idempotent ⟩,
  comp := λ X Y Z f g, ⟨ f.morphism ≫ g.morphism ⟩ }

namespace IdempotentCompletion

def functor_to_completion (C : Type (u+1)) [large_category C] : C ⥤ (Idempotent C) := 
{ obj := λ X, { object := X, idempotent := 𝟙 X },
  map' := λ _ _ f, { morphism := f } }

-- -- PROJECT
-- def IdempotentCompletion_functorial (C : Type u) [category C] (D : Type u) [category D] : Functor (Functor C D) (Functor (Idempotent C) (Idempotent D)) := {

lemma embedding (C : Type (u+1)) [large_category C]  : embedding (functor_to_completion C) := by obviously

variable {D : Type (u₂+1)}
variable [large_category D]

def restrict_Functor_from (F : (Idempotent C) ⥤ D) : C ⥤ D :=
  (functor_to_completion C) ⋙ F

@[simp] private lemma double_idempotent_morphism_left (X Y : Idempotent (Idempotent C)) (f : X ⟶ Y)
  : (X.idempotent).morphism ≫ (f.morphism).morphism = (f.morphism).morphism := congr_arg Idempotent.morphism.morphism f.left
@[simp] private lemma double_idempotent_morphism_right (X Y : Idempotent (Idempotent C)) (f : X ⟶ Y)
  : (f.morphism).morphism ≫ (Y.idempotent).morphism = (f.morphism).morphism := congr_arg Idempotent.morphism.morphism f.right

private def idempotent_functor (C : Type (u+1)) [large_category C] : (Idempotent (Idempotent C)) ⥤ (Idempotent C) :=
{ obj := λ X, ⟨ X.object.object, X.idempotent.morphism, congr_arg Idempotent.morphism.morphism X.witness ⟩, -- PROJECT think about automation here
  map' := λ X Y f, ⟨ f.morphism.morphism, by obviously ⟩ }
private def idempotent_inverse (C : Type (u+1)) [large_category C] : (Idempotent C) ⥤ (Idempotent (Idempotent C)) :=
{ obj := λ X, ⟨ X, ⟨ X.idempotent, by obviously ⟩, by obviously ⟩,
  map' := λ X Y f, ⟨ f, by obviously ⟩ }

-- PROJECT prove these lemmas about idempotent completion

-- lemma IdempotentCompletion_idempotent (C : Type u) [category C] :
--   Equivalence (IdempotentCompletion (IdempotentCompletion C)) (IdempotentCompletion C) :=
-- {
--   functor := IdempotentCompletion_idempotent_functor C,
--   inverse := IdempotentCompletion_idempotent_inverse C,
--   isomorphism_1 := begin tidy, exact C.identity _, tidy, induction f_2, tidy, end, -- PROJECT very slow??
--   isomorphism_2 := sorry
--}

def extend_Functor_to_completion (F : C ⥤ (Idempotent D)) : (Idempotent C) ⥤ (Idempotent D) :=
{ obj := λ X, { object := (F X.object).object, 
                idempotent := (F.map X.idempotent).morphism },
  map' := λ X Y f, { morphism := (F.map f.morphism).morphism } }

-- lemma Functor_from_IdempotentCompletion_determined_by_restriction 
--   {C D : Category} (F : Functor (IdempotentCompletion C) (IdempotentCompletion D)) :
--     NaturalIsomorphism (extend_Functor_to_IdempotentCompletion (restrict_Functor_from_IdempotentCompletion F)) F := 
--       sorry

-- PROJECT idempotent completion left adjoint to the forgetful functor from categories to semicategories?

end IdempotentCompletion
end category_theory
