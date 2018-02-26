-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .functor
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
-- private meta def induction_WalkingPair : tactic unit :=
-- do l ← local_context,
--    at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(WalkingPair) := induction h >> skip | _ := failed end))

-- attribute [tidy] induction_WalkingPair

-- instance decidable_eq_WalkingPair : decidable_eq WalkingPair := ♯

-- instance WalkingPair_category : category WalkingPair := {
--   Hom := begin
--            intros X Y,
--            induction X,
--            {induction Y, exact punit, exact pempty},
--            {induction Y, exact pempty, exact punit}
--          end,
--   identity       := by tidy,
--   compose        := begin
--                       intros X Y Z f g, induction X ; induction Y ; induction Z ; dsimp at *, 
--                       exact punit.star, exact g, exact punit.star, exact f, induction f, exact punit.star, induction g, exact punit.star
--                     end
-- }
instance WalkingPair_category : category WalkingPair := {
  Hom := λ X Y, match X, Y with
                | _1, _1 := punit
                | _2, _2 := punit
                | _ , _  := pempty
                end,
  identity       := begin intros, cases X, split, split, end,
  compose        := begin
                      intros X Y Z f g, cases X; cases Y; cases Z; cases f; cases g; exact punit.star
                    end,
  left_identity := begin dsimp, intros, cases X; cases Y; cases f; apply punits_equal end,
  right_identity := begin dsimp, intros, cases X; cases Y; cases f; apply punits_equal end,
  associativity := begin dsimp, intros, cases W; cases X; cases Y; cases Z; cases f; cases g; cases h; apply punits_equal end,
}


local attribute [applicable] category.identity

variable {C : Type (u₁+1)}
variable [category C]

-- @[simp] lemma Hom_1_2 : Hom _1 _2 = pempty := begin dunfold Hom, tidy, end
-- @[simp] lemma Hom_2_1 : Hom _2 _1 = pempty := begin dunfold Hom, tidy, end

definition Pair_functor (α β : C) : Functor WalkingPair C := {
  onObjects     := λ X, match X with
                   | _1 := α
                   | _2 := β
                   end,
  onMorphisms   := λ X Y f, match X, Y, f with
                   | _1, _1, _ := 1
                   | _2, _2, _ := 1
                   end,
  identities := begin dsimp, intros, cases X; refl, end,
  functoriality := begin dsimp, intros, cases X; cases Y; cases Z; cases f; cases g; unfold Pair_functor._match_2; simp, end,
}
-- definition Pair_functor (α β : C) : Functor WalkingPair C := {
--   onObjects     := begin intros X, induction X, exact α, exact β end,
--   onMorphisms   := begin
--                      intros,
--                      induction X,
--                      {induction Y,
--                        {exact 𝟙 α},
--                        {induction a}},
--                      {induction Y,
--                        {induction a},
--                        {exact 𝟙 β}}
--                    end,
-- }
end

section
inductive WalkingParallelPair : Type u₁
| _1
| _2

open WalkingParallelPair

-- open tactic
-- meta def induction_WalkingParallelPair : tactic unit :=
-- do l ← local_context,
--    at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(WalkingParallelPair) := induction h >> skip | _ := failed end))

-- attribute [tidy] induction_WalkingParallelPair

-- instance decidable_eq_WalkingParallelPair : decidable_eq WalkingParallelPair := ♯

-- instance : category WalkingParallelPair := {
--   Hom := begin
--            intros X Y,
--            induction X,
--            {induction Y, exact punit, exact Two},
--            {induction Y, exact pempty, exact punit}
--          end,
--   identity       := by tidy,
--   compose        := begin
--                       intros X Y Z f g, induction X ; induction Y ; induction Z ; dsimp at *, 
--                       exact punit.star, exact g, exact punit.star, exact f, induction f, exact punit.star, induction g, exact punit.star
--                     end
-- }
instance : category WalkingParallelPair := {
  Hom := λ X Y, match X, Y with
         | _1, _1 := punit
         | _2, _2 := punit
         | _1, _2 := Two
         | _2, _1 := pempty
         end,
  identity       := begin intros, cases X, split, split, end,
  compose        := begin
                      intros X Y Z f g, cases X ; cases Y ; cases Z, 
                      exact punit.star, exact g, exact punit.star, exact f, cases f, exact punit.star, cases g, exact punit.star
                    end,
  left_identity := begin dsimp, intros, cases X; cases Y; simp, any_goals { apply punits_equal }, cases f, end,
  right_identity := begin dsimp, intros, cases X; cases Y; simp, any_goals { apply punits_equal }, cases f, end,
  associativity := begin dsimp, intros, cases W; cases X; cases Y; cases Z; simp, cases g, cases f, cases f, cases h, end                  
}

variable {C : Type (u₁+1)}
variable [category C]



definition ParallelPair_functor {α β : C} (f g : Hom α β) : Functor WalkingParallelPair C := {
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
  identities := begin dsimp, intros, cases X; unfold ParallelPair_functor._match_2; refl, end,
  functoriality := begin dsimp, intros, cases X; cases Y; cases Z; simp; cases f_1; cases g_1; unfold ParallelPair_functor._match_2, any_goals { rw category.identity_idempotent' }, any_goals { erw category.left_identity_lemma' }, any_goals { erw category.right_identity_lemma' }, end
}
-- -- this style is obscene. FIXME learn to use match statements  (or rather, to automatically unfold them)
-- definition ParallelPair_functor {α β : C} (f g : Hom α β) : Functor WalkingParallelPair C := 
-- {
--   onObjects     := begin intros X, induction X, exact α, exact β end,
--   onMorphisms   := begin
--                      intros,
--                      induction X,
--                      {induction Y,
--                        {exact 𝟙 α},
--                        {induction a, exact f, exact g}},
--                      {induction Y,
--                        {induction a},
--                        {exact 𝟙 β}}
--                    end,
--   functoriality := begin tidy, any_goals { induction f_1 }, any_goals { induction g_1 },  end
-- }
end

end categories.walking

