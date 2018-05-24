-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.walking
import categories.discrete_category
import categories.universal.initial

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.initial
open categories.walking

namespace categories.comma

universes j u₁ u₂ u₃

-- The diagonal functor sends X to the constant functor that sends everything to X.
definition DiagonalFunctor (J : Type j) [small_category J] (C : Type (u₁+1)) [category C] : C ↝ (J ↝ C) :=
{
  onObjects     := λ X : C, {
    onObjects     := λ _, X,
    onMorphisms   := λ _ _ _, 𝟙 X
 },
  onMorphisms   := λ X Y f, {
    components := λ _, f
 }
}

section
local attribute [ematch] subtype.property

variable {A : Type u₁}
variable [small_category A]
variable {B : Type u₂}
variable [small_category B]
variable {C : Type (u₃+1)}
variable [category C]

definition comma (S : A ↝ C) (T : B ↝ C) : Type (max u₁ u₂ u₃) := Σ p : A × B, (S +> p.1) ⟶ (T +> p.2)

structure comma_morphism {S : A ↝ C} {T : B ↝ C} (p q : comma S T) : Type (max u₁ u₂ u₃) :=
(left : p.1.1 ⟶ q.1.1)
(right : p.1.2 ⟶ q.1.2)
(condition : (S &> left) ≫ q.2 = p.2 ≫ (T &> right) . obviously)

make_lemma comma_morphism.condition
attribute [ematch] comma_morphism.condition_lemma

@[applicable] lemma comma_morphism_equal
  {S : A ↝ C} {T : B ↝ C} {p q : comma S T} (f g : comma_morphism p q)
  (wl : f.left = g.left) (wr : f.right = g.right) : f = g :=
  begin
    induction f,
    induction g,
    tidy,
  end

instance CommaCategory (S : A ↝ C) (T : B ↝ C) : small_category (comma S T) := {
  Hom      := λ p q, comma_morphism p q,
  identity := λ p, ⟨ 𝟙 p.1.1, 𝟙 p.1.2, by obviously ⟩,
  compose  := λ p q r f g, ⟨ f.left ≫ g.left, f.right ≫ g.right, by obviously ⟩
}

-- cf Leinster Remark 2.3.2
definition CommaCategory_left_projection (S : A ↝ C) (T : B ↝ C) : (comma S T) ↝ A := {
  onObjects     := λ X, X.1.1,
  onMorphisms   := λ _ _ f, f.left
}

definition CommaCategory_right_projection (S : A ↝ C) (T : B ↝ C) : (comma S T) ↝ B := {
  onObjects     := λ X, X.1.2,
  onMorphisms   := λ _ _ f, f.right
}

definition CommaCategory_projection_transformation
  (S : A ↝ C) (T : B ↝ C)
    : ((CommaCategory_left_projection S T) ⋙ S) ⟹ ((CommaCategory_right_projection S T) ⋙ T) := {
      components := λ X, X.2
   }


definition ObjectAsFunctor (X : C) : punit ↝ C := 
{ onObjects     := λ _, X,
  onMorphisms   := λ _ _ _, 𝟙 X }

instance : has_coe C (punit ↝ C) :=
{ coe := ObjectAsFunctor }

definition SliceCategory   (X : C) : category (comma (1 : C ↝ C) (X : punit ↝ C)) := by apply_instance
definition CosliceCategory (X : C) : category (comma (X : punit ↝ C) (1 : C ↝ C)) := by apply_instance
end

-- In Cones, we have
--   A = C
--   B = .
--   C = FunctorCategory J C
variable {J : Type j}
variable [small_category J]
variable {C : Type (u₁+1)}
variable [category C]

definition Cone   (F : Functor J C) := (comma (DiagonalFunctor.{j u₁} J C) (ObjectAsFunctor F))
definition Cocone (F : Functor J C) := (comma (ObjectAsFunctor F)          (DiagonalFunctor.{j u₁} J C))

@[simp] lemma Cone_comma_unit   (F : Functor J C) (X : Cone F) : X.1.2 = punit.star := by obviously 
@[simp] lemma Cocone_comma_unit (F : Functor J C) (X : Cocone F) : X.1.1 = punit.star := by obviously 

instance Cones   (F : Functor J C) : category (Cone F)   := begin unfold Cone, apply_instance end
instance Cocones (F : Functor J C) : category (Cocone F) := begin unfold Cocone, apply_instance end

definition Limit   (F: Functor J C) := TerminalObject (Cone   F)
definition Colimit (F: Functor J C) := InitialObject  (Cocone F)

definition BinaryProduct   (α β : C)                  := Limit   (Pair_functor α β)
definition BinaryCoproduct (α β : C)                  := Colimit (Pair_functor α β)
definition Product         {I : Type (u₁+1)} (X : I → C) := Limit   (Functor.fromFunction X)
definition Coproduct       {I : Type (u₁+1)} (X : I → C) := Colimit (Functor.fromFunction X)
definition Equalizer       {α β : C} (f g : α ⟶ β)  := Limit   (ParallelPair_functor f g)
definition Coequalizer     {α β : C} (f g : α ⟶ β)  := Colimit (ParallelPair_functor f g)

end categories.comma

