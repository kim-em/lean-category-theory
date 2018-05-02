-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.functor
import categories.util.finite
import data.fintype

open categories
open categories.functor
open categories.util.finite

namespace categories.walking

universes u₁ u₂

section
inductive WalkingPair : Type u₁
| _1
| _2

open WalkingPair

section
open tactic
@[tidy] private meta def induction_WalkingPair : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(WalkingPair) := cases h >> skip | _ := failed end)),
   skip
end

attribute [tidy] induction_WalkingPair


instance decidable_eq_WalkingPair : decidable_eq WalkingPair := by dsimp [decidable_eq, decidable_rel]; obviously
instance fintype_WalkingPair : fintype WalkingPair := {
  elems := [_1, _2].to_finset,
  complete := sorry  -- FIXME dsimp and unfold_coes loops.
}

open tactic
private meta def case_bash : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, cases h >> skip)),
   skip

local attribute [tidy] case_bash

@[reducible] def WalkingPair.hom : WalkingPair → WalkingPair → Type u₁ 
| _1 _1 := punit
| _2 _2 := punit
| _  _  := pempty
attribute [reducible] WalkingPair.hom._main

instance (X Y : WalkingPair) : decidable_eq (WalkingPair.hom X Y) := by dsimp [decidable_eq, decidable_rel]; obviously

instance WalkingPair_category : small_category WalkingPair := {
  Hom := WalkingPair.hom,
  identity       := by tidy,
  compose        := by tidy
}

local attribute [applicable] uv_category.identity

variable {C : Type (u₁+1)}
variable [category C]

@[reducible] def Pair_functor.onObjects (α β : C) : WalkingPair → C
| _1 := α
| _2 := β 
attribute [reducible] Pair_functor.onObjects._main
@[reducible] def Pair_functor.onMorphisms (α β : C) (X Y : WalkingPair) (f : X ⟶ Y) : (Pair_functor.onObjects α β X) ⟶ (Pair_functor.onObjects α β Y) :=
match X, Y, f with
| _1, _1, _ := 𝟙 α 
| _2, _2, _ := 𝟙 β
end
attribute [reducible] Pair_functor.onMorphisms._match_1

definition Pair_functor (α β : C) : Functor WalkingPair.{u₁+1} C := {
  onObjects     := Pair_functor.onObjects α β,
  onMorphisms   := Pair_functor.onMorphisms α β,
}

definition Pair_functor' (α β : C) : Functor WalkingPair.{u₁+1} C := {
  onObjects     := λ X, match X with 
                   | _1 := α 
                   | _2 := β
                   end,
  onMorphisms   := λ X Y f, match X, Y, f with
                   | _1, _1, _ := 𝟙 α 
                   | _2, _2, _ := 𝟙 β
                   end,
}
end

section
inductive WalkingParallelPair : Type u₁
| _1
| _2

open WalkingParallelPair



section
open tactic
private meta def induction_WalkingParallelPair : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(WalkingParallelPair) := cases h >> skip | _ := failed end)),
   skip
   
attribute [tidy] induction_WalkingParallelPair
end

local attribute [tidy] case_bash

instance : small_category WalkingParallelPair := {
  Hom := λ X Y, match X, Y with
         | _1, _1 := punit
         | _2, _2 := punit
         | _1, _2 := Two
         | _2, _1 := pempty
         end,
  identity       := by tidy,
  compose        := λ X Y Z f g, match X, Y, Z, f, g with
                    | _1, _1, _1, _, _ := punit.star
                    | _2, _2, _2, _, _ := punit.star
                    | _1, _1, _2, _, h := h
                    | _1, _2, _2, h, _ := h
                    end
}

variable {C : Type (u₁+1)}
variable [category C]

definition ParallelPair_functor {α β : C} (f g : α ⟶ β) : WalkingParallelPair ↝ C := {
  onObjects     := λ X, match X with
                   | _1 := α
                   | _2 := β
                   end,
  onMorphisms   := λ X Y h, match X, Y, h with
                   | _1, _1, _ := 1
                   | _2, _2, _ := 1
                   | _1, _2, Two._0 := f
                   | _1, _2, Two._1 := g
                   end,
}
end

end categories.walking

