-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .discrete_category
import .util.finite

open categories
open categories.functor
open categories.util.finite

namespace categories.walking

universes u₁ u₂

instance subsingleton_pempty : subsingleton pempty :=
begin
tidy,
end
instance subsingleton_punit : subsingleton punit :=
begin
tidy,
end

instance unit_or_empty_subsingleton {α : Type u₁} [decidable_eq α] {a b : α} : subsingleton (ite (a = b) punit pempty) :=
begin
by_cases a = b,
rw h,
simp,
apply_instance,
rw if_neg h,
apply_instance,
end
local attribute [applicable] subsingleton.elim

section
inductive WalkingPair : Type u₁
| _1
| _2

open WalkingPair

@[simp] lemma WalkingPair_1_eq_2_eq_false : (_1 = _2) ↔ false :=
by tidy

@[simp] lemma WalkingPair_2_eq_1_eq_false : (_2 = _1) ↔ false :=
by tidy

@[simp] lemma WalkingPair_1_eq_1_eq_false : (_1 = _1) ↔ true :=
by tidy

@[simp] lemma WalkingPair_2_eq_2_eq_false : (_2 = _2) ↔ true :=
by tidy


open tactic
private meta def induction_WalkingPair : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(WalkingPair) := induction h >> skip | _ := failed end))

local attribute [tidy] induction_WalkingPair

instance decidable_eq_WalkingPair : decidable_eq WalkingPair := ♯

instance WalkingPair_category : category WalkingPair := {
  Hom := begin
           intros X Y,
           induction X,
           {induction Y, exact punit, exact pempty},
           {induction Y, exact pempty, exact punit}
         end,
  identity       := by tidy,
  compose        := begin
                      intros X Y Z f g, induction X ; induction Y ; induction Z ; dsimp at *, 
                      exact punit.star, exact g, exact punit.star, exact f, induction f, exact punit.star, induction g, exact punit.star
                    end
}

-- {
--   Hom := λ X Y, if X = Y then punit else pempty,
--   identity       := by tidy, 
--   compose        := by tidy,
-- }

local attribute [applicable] category.identity

variable {C : Type u₁}
variable [category C]

@[simp] lemma Hom_1_2 : Hom _1 _2 = pempty := begin dunfold Hom, tidy, end
@[simp] lemma Hom_2_1 : Hom _2 _1 = pempty := begin dunfold Hom, tidy, end

definition Pair_functor (α β : C) : Functor WalkingPair C := {
  onObjects     := begin intros X, induction X, exact α, exact β end,
  onMorphisms   := begin
                     intros,
                     induction X,
                     {induction Y,
                       {exact 𝟙 α},
                       {induction a}},
                     {induction Y,
                       {induction a},
                       {exact 𝟙 β}}
                   end,
}
end

section
inductive WalkingParallelPair : Type u₁
| _1
| _2

open WalkingParallelPair

open tactic
meta def induction_WalkingParallelPair : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(WalkingParallelPair) := induction h >> skip | _ := failed end))

local attribute [tidy] induction_WalkingParallelPair

instance decidable_eq_WalkingParallelPair : decidable_eq WalkingParallelPair := ♯

instance : category WalkingParallelPair := {
  Hom := begin
           intros X Y,
           induction X,
           {induction Y, exact punit, exact Two},
           {induction Y, exact pempty, exact punit}
         end,
  identity       := by tidy,
  compose        := begin
                      intros X Y Z f g, induction X ; induction Y ; induction Z ; dsimp at *, 
                      exact punit.star, exact g, exact punit.star, exact f, induction f, exact punit.star, induction g, exact punit.star
                    end
}

variable {C : Type u₁}
variable [category C]

-- this style is obscene. FIXME learn to use match statements  (or rather, to automatically unfold them)
definition ParallelPair_functor {α β : C} (f g : Hom α β) : Functor WalkingParallelPair C := 
{
  onObjects     := begin intros X, induction X, exact α, exact β end,
  onMorphisms   := begin
                     intros,
                     induction X,
                     {induction Y,
                       {exact 𝟙 α},
                       {induction a, exact f, exact g}},
                     {induction Y,
                       {induction a},
                       {exact 𝟙 β}}
                   end,
  functoriality := begin tidy, any_goals { induction f_1 }, any_goals { induction g_1 },  end
}
end

end categories.walking

