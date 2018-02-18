-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..walking
import .initial

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
definition DiagonalFunctor (J : Type j) [category J] (C : Type u₁) [category C] : Functor C (Functor J C) :=
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
variable [category A]
variable {B : Type u₂}
variable [category B]
variable {C : Type u₃}
variable [category C]

definition comma (S : Functor A C) (T : Functor B C) := Σ p : A × B, Hom (S.onObjects p.1) (T.onObjects p.2)

structure comma_morphism {S : Functor A C} {T : Functor B C} (p q : comma S T) : Type (max u₁ u₂ u₃) :=
(left : Hom p.1.1 q.1.1)
(right : Hom p.1.2 q.1.2)
(condition : (S.onMorphisms left) ≫ q.2 = p.2 ≫ (T.onMorphisms right) . obviously)

make_lemma comma_morphism.condition
attribute [ematch] comma_morphism.condition_lemma

@[applicable] lemma comma_morphism_equal
  {S : Functor A C} {T : Functor B C} {p q : comma S T} (f g : comma_morphism p q)
  (wl : f.left = g.left) (wr : f.right = g.right) : f = g :=
  begin
    induction f,
    induction g,
    tidy,
  end


instance CommaCategory (S : Functor A C) (T : Functor B C) : category (comma S T) := {
  Hom      := λ p q, comma_morphism p q,
  identity := λ p, ⟨ 𝟙 p.1.1, 𝟙 p.1.2, ♮ ⟩,
  compose  := λ p q r f g, ⟨ f.left ≫ g.left, f.right ≫ g.right, ♯ ⟩
}

-- cf Leinster Remark 2.3.2
definition CommaCategory_left_projection (S : Functor A C) (T : Functor B C) : Functor (comma S T) A := {
  onObjects     := λ X, X.1.1,
  onMorphisms   := λ _ _ f, f.left
}

definition CommaCategory_right_projection (S : Functor A C) (T : Functor B C) : Functor (comma S T) B := {
  onObjects     := λ X, X.1.2,
  onMorphisms   := λ _ _ f, f.right
}

definition CommaCategory_projection_transformation
  (S : Functor A C) (T : Functor B C)
    : NaturalTransformation (FunctorComposition (CommaCategory_left_projection S T) S) (FunctorComposition (CommaCategory_right_projection S T) T) := {
      components := λ X, X.2
   }


definition ObjectAsFunctor (X : C) : Functor punit C :=
{
  onObjects     := λ _, X,
  onMorphisms   := λ _ _ _, 𝟙 X
}

definition SliceCategory   (X : C) : category (comma (IdentityFunctor C) (ObjectAsFunctor X)) := by apply_instance
definition CosliceCategory (X : C) : category (comma (ObjectAsFunctor X) (IdentityFunctor C)) := by apply_instance
end

-- In Cones, we have
--   A = C
--   B = .
--   C = FunctorCategory J C
variable {J : Type j}
variable [category J]
variable {C : Type u₁}
variable [category C]

definition Cone (F : Functor J C)   := (comma (DiagonalFunctor.{j u₁} J C) (ObjectAsFunctor F))
definition Cocone (F : Functor J C) := (comma (ObjectAsFunctor F)          (DiagonalFunctor.{j u₁} J C))

instance Cones   (F : Functor J C) : category (Cone F)   := begin unfold Cone, apply_instance end
instance Cocones (F : Functor J C) : category (Cocone F) := begin unfold Cocone, apply_instance end

definition Limit   (F: Functor J C) := TerminalObject (Cone   F)
definition Colimit (F: Functor J C) := InitialObject  (Cocone F)

-- TODO clean this up: WalkingPair and WalkingParallelPair should just have different object types
definition BinaryProduct   (α β : C)                  := @Limit  _ WalkingPair _ _ (Pair_functor α β)
definition BinaryCoproduct (α β : C)                  := @Colimit _ WalkingPair _ _ (Pair_functor α β)
definition Product         {I : Type u₁} (X : I → C) := Limit   (Functor.fromFunction X)
definition Coproduct       {I : Type u₁} (X : I → C) := Colimit (Functor.fromFunction X)
definition Equalizer       {α β : C} (f g : Hom α β)  := @Limit   _ WalkingParallelPair _ _ (ParallelPair_functor f g)
definition Coequalizer     {α β : C} (f g : Hom α β)  := @Colimit _ WalkingParallelPair _ _ (ParallelPair_functor f g)

end categories.comma

