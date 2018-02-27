-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .functor
import .util.finite
import data.fintype

open categories
open categories.functor
open categories.util.finite

namespace categories.walking

universes u₁ u₂

-- move to lean-tidy
instance subsingleton_pempty : subsingleton pempty :=
begin
tidy,
end
instance subsingleton_punit : subsingleton punit :=
begin
tidy,
end

attribute [applicable] subsingleton.elim
--

section
inductive WalkingPair : Type u₁
| _1
| _2

open WalkingPair




open tactic
private meta def induction_WalkingPair : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(WalkingPair) := cases h >> skip | _ := failed end))

attribute [tidy] induction_WalkingPair

instance decidable_eq_WalkingPair : decidable_eq WalkingPair := ♯
instance fintype_WalkingPair : fintype WalkingPair := {
  elems := [_1, _2].to_finset,
  complete := begin intros, cases x; simp end
}

@[reducible] def WalkingPair.hom : WalkingPair → WalkingPair → Type u₁ 
| _1 _1 := punit
| _2 _2 := punit
| _  _  := pempty
attribute [reducible] WalkingPair.hom._main

instance (X Y : WalkingPair) : decidable_eq (WalkingPair.hom X Y) := λ f g, begin cases X; cases Y; cases f; cases g; simp; apply_instance end

instance WalkingPair_category : category WalkingPair := {
  Hom := WalkingPair.hom,
  identity       := by tidy,
  compose        := by tidy
}

local attribute [applicable] category.identity

variable {C : Type (u₁+1)}
variable [category C]

-- PROJECT improve automation
definition Pair_functor (α β : C) : Functor WalkingPair C := {
  onObjects     := λ X, match X with
                   | _1 := α
                   | _2 := β
                   end,
  onMorphisms   := λ X Y f, match X, Y, f with
                   | _1, _1, _ := 1
                   | _2, _2, _ := 1
                   end,
  functoriality := begin dsimp, intros, cases X; cases Y; cases Z; cases f; cases g; unfold Pair_functor._match_2; simp, end,
}
end

section
inductive WalkingParallelPair : Type u₁
| _1
| _2

open WalkingParallelPair

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
end

end categories.walking

