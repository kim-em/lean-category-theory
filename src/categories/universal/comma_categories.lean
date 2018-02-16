-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..walking
import .initial

open categories
open categories.isomorphism
open categories.graphs
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.initial
open categories.walking

namespace categories.comma

universes j u₁ u₂ u₃

-- The diagonal functor sends X to the constant functor that sends everything to X.
definition DiagonalFunctor {J : Type j} [category J] {C : Type u₁} [category C] : Functor C (Functor J C) :=
{
  onObjects     := λ X : C, {
    onObjects     := λ _, X,
    onMorphisms   := λ _ _ _, 𝟙 X
 },
  onMorphisms   := λ X Y f, {
    components := λ _, f
 }
}

-- unfortunately one can't coerce along subtype.val
open subtype

local attribute [ematch] subtype.property

-- The elaborator has some trouble understanding what p.2.2 and q.2.2 mean below.
-- Leo suggested the following work-around, at <https://groups.google.com/d/msg/lean-user/8jW4BIUFl24/MOtgbpfqCAAJ>.
-- local attribute [elab_simple]  sigma.snd

variable {J : Type u₁}
variable [category J]
variable {A : Type u₁}
variable [category A]
variable {B : Type u₁}
variable [category B]
variable {C : Type u₁}
variable [category C]

definition comma (S : Functor A C) (T : Functor B C) := Σ a : A, Σ b : B, Hom (S.onObjects a) (T.onObjects b)

instance CommaCategory (S : Functor A C) (T : Functor B C) : category (comma S T) := {
  Hom      := λ p q, {gh : (Hom p.1 q.1) × (Hom p.2.1 q.2.1) // (S.onMorphisms gh.1) ≫ q.2.2 = p.2.2 ≫ (T.onMorphisms gh.2)},
  identity := λ p, ⟨ (𝟙 p.1, 𝟙 p.2.1), ♮ ⟩,
  compose  := λ p q r f g, ⟨ ((val f).1 ≫ (val g).1, (val f).2 ≫ (val g).2), ♮ ⟩
}

-- cf Leinster Remark 2.3.2
definition CommaCategory_left_projection (S : Functor A C) (T : Functor B C) : Functor (comma S T) A := {
  onObjects     := λ X, X.1,
  onMorphisms   := λ _ _ f, f.val.1
}

definition CommaCategory_right_projection (S : Functor A C) (T : Functor B C) : Functor (comma S T) B := {
  onObjects     := λ X, X.2.1,
  onMorphisms   := λ _ _ f, f.val.2
}

definition CommaCategory_projection_transformation
  (S : Functor A C) (T : Functor B C)
    : NaturalTransformation (FunctorComposition (CommaCategory_left_projection S T) S) (FunctorComposition (CommaCategory_right_projection S T) T) := {
      components := λ X, X.2.2
   }


definition ObjectAsFunctor (X : C) : Functor (DiscreteCategory unit) C :=
{
  onObjects     := λ _, X,
  onMorphisms   := λ _ _ _, 𝟙 X
}

definition SliceCategory   (X : C.Obj) := CommaCategory (IdentityFunctor C) (ObjectAsFunctor X)
definition CosliceCategory (X : C.Obj) := CommaCategory (ObjectAsFunctor X) (IdentityFunctor C)

-- In Cones, we have
--   A = C
--   B = .
--   C = FunctorCategory J C
definition Cones   (F : Functor J C) := CommaCategory (DiagonalFunctor J C)                      (ObjectAsFunctor F)
definition Cocones (F : Functor J C) := CommaCategory (@ObjectAsFunctor (FunctorCategory J C) F) (DiagonalFunctor J C)

definition Limit   (F: Functor J C) := TerminalObject (Cones   F)
definition Colimit (F: Functor J C) := InitialObject  (Cocones F)

definition BinaryProduct   (α β : C)                  := Limit   (Pair_functor α β)
definition BinaryCoproduct (α β : C)                  := Colimit (Pair_functor α β)
definition Product         {I : Type u₁} (X : I → C) := Limit   (Functor.fromFunction X)
definition Coproduct       {I : Type u₁} (X : I → C) := Colimit (Functor.fromFunction X)
definition Equalizer       {α β : C} (f g : Hom α β)  := Limit   (ParallelPair_functor f g)
definition Coequalizer     {α β : C} (f g : Hom α β)  := Colimit (ParallelPair_functor f g)

end categories.comma

