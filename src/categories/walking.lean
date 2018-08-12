-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor
import data.fintype
import categories.util.Two

open category_theory

namespace category_theory.walking

universes u₁ v₁ u₂ v₂

section
@[derive decidable_eq]
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


-- instance fintype_WalkingPair : fintype WalkingPair := {
--   elems := [_1, _2].to_finset,
--   complete := by obviously
-- }

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

instance WalkingPair_category : small_category WalkingPair := 
{ Hom  := WalkingPair.hom,
  id   := by tidy,
  comp := by tidy }

local attribute [backwards] category.id

variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞

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

def Pair_functor (α β : C) : WalkingPair.{v₁} ↝ C := 
{ obj := Pair_functor.onObjects α β,
  map := Pair_functor.onMorphisms α β, }

def Pair_functor' (α β : C) : WalkingPair.{v₁} ↝ C := 
{ obj := λ X, match X with 
              | _1 := α 
              | _2 := β
              end,
  map := λ X Y f, match X, Y, f with
                  | _1, _1, _ := 𝟙 α 
                  | _2, _2, _ := 𝟙 β
                  end, }
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

instance : small_category WalkingParallelPair := 
{ Hom := λ X Y, match X, Y with
                | _1, _1 := punit
                | _2, _2 := punit
                | _1, _2 := Two
                | _2, _1 := pempty
                end,
  id       := by tidy,
  comp  := λ X Y Z f g, match X, Y, Z, f, g with
                        | _1, _1, _1, _, _ := punit.star
                        | _2, _2, _2, _, _ := punit.star
                        | _1, _1, _2, _, h := h
                        | _1, _2, _2, h, _ := h
                        end }

variable {C : Type u₁}
variable [category.{u₁ v₁} C]

def ParallelPair_functor {α β : C} (f g : α ⟶ β) : WalkingParallelPair.{v₁} ↝ C := 
{ obj := λ X, match X with
              | _1 := α
              | _2 := β
              end,
  map := λ X Y h, match X, Y, h with
                  | _1, _1, _ := 𝟙 α
                  | _2, _2, _ := 𝟙 β
                  | _1, _2, Two._0 := f
                  | _1, _2, Two._1 := g
                  end, }
end

end category_theory.walking

