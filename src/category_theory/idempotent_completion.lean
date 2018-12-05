-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.equivalence

namespace category_theory

universes u u₁ u₂

structure idempotent (C : Type (u+1)) [large_category C] :=
(X : C)
(idem : X ⟶ X)
(w' : idem ≫ idem = idem . obviously)

restate_axiom idempotent.w'
attribute [simp,search] idempotent.w

variables {C : Type (u+1)} [large_category C]

namespace idempotent

structure morphism (P Q : idempotent C) :=
(hom : P.X ⟶ Q.X)
(left' : P.idem ≫ hom = hom . obviously)
(right' : hom ≫ Q.idem = hom . obviously)

restate_axiom morphism.left'
restate_axiom morphism.right'
attribute [simp,search] morphism.left morphism.right

@[extensionality] lemma ext {P Q : idempotent C} (f g : morphism P Q) (w : f.hom = g.hom) : f = g :=
begin
  induction f,
  induction g,
  tidy
end

end idempotent

instance idempotent_completion : large_category (idempotent C) :=
{ hom  := idempotent.morphism,
  id   := λ P, ⟨ P.idem ⟩,
  comp := λ _ _ _ f g, ⟨ f.hom ≫ g.hom ⟩ }

namespace idempotent_completion

def functor_to_completion (C : Type (u+1)) [large_category C] : C ⥤ (idempotent C) :=
{ obj := λ P, { X := P, idem := 𝟙 P },
  map := λ _ _ f, { hom := f } }

-- -- PROJECT
-- def IdempotentCompletion_functorial (C : Type u) [category C] (D : Type u) [category D] : Functor (Functor C D) (Functor (Idempotent C) (Idempotent D)) := {

-- FIXME
-- lemma embedding' (C : Type (u+1)) [large_category C]  : embedding (functor_to_completion C) := by obviously

variable {D : Type (u₂+1)}
variable [large_category D]

def restrict_Functor_from (F : (idempotent C) ⥤ D) : C ⥤ D :=
(functor_to_completion C) ⋙ F

@[simp] private lemma double_idempotent_morphism_left (P Q : idempotent (idempotent C)) (f : P ⟶ Q)
  : (P.idem).hom ≫ (f.hom).hom = (f.hom).hom := congr_arg idempotent.morphism.hom f.left
@[simp] private lemma double_idempotent_morphism_right (P Q : idempotent (idempotent C)) (f : P ⟶ Q)
  : (f.hom).hom ≫ (Q.idem).hom = (f.hom).hom := congr_arg idempotent.morphism.hom f.right

private def idempotent_functor (C : Type (u+1)) [large_category C] : (idempotent (idempotent C)) ⥤ (idempotent C) :=
{ obj := λ P, ⟨ P.X.X, P.idem.hom, congr_arg idempotent.morphism.hom P.w ⟩, -- PROJECT think about automation here
  map := λ _ _ f, ⟨ f.hom.hom, by obviously ⟩ }
private def idempotent_inverse (C : Type (u+1)) [large_category C] : (idempotent C) ⥤ (idempotent (idempotent C)) :=
{ obj := λ P, ⟨ P, ⟨ P.idem, by obviously ⟩, by obviously ⟩,
  map := λ _ _ f, ⟨ f, by obviously ⟩ }

-- PROJECT prove these lemmas about idempotent completion

-- lemma IdempotentCompletion_idempotent (C : Type u) [category C] :
--   equivalence (IdempotentCompletion (IdempotentCompletion C)) (IdempotentCompletion C) :=
-- {
--   functor := IdempotentCompletion_idempotent_functor C,
--   inverse := IdempotentCompletion_idempotent_inverse C,
--   isomorphism_1 := begin tidy, exact C.identity _, tidy, induction f_2, tidy, end, -- PROJECT very slow??
--   isomorphism_2 := sorry
--}

def extend_Functor_to_completion (F : C ⥤ (idempotent D)) : (idempotent C) ⥤ (idempotent D) :=
{ obj := λ P,
  { X := (F.obj P.X).X,
    idem := (F.map P.idem).hom },
  map := λ _ _ f, { morphism := (F.map f.hom).hom } }

-- lemma Functor_from_IdempotentCompletion_determined_by_restriction
--   {C D : Category} (F : Functor (IdempotentCompletion C) (IdempotentCompletion D)) :
--     NaturalIsomorphism (extend_Functor_to_IdempotentCompletion (restrict_Functor_from_IdempotentCompletion F)) F :=
--       sorry

-- PROJECT idempotent completion left adjoint to the forgetful functor from categories to semicategories?

end idempotent_completion
end category_theory
