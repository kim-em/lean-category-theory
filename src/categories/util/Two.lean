-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.tidy

universes u v

open tactic

inductive Two : Type u
| _0 : Two
| _1 : Two

open Two

@[simp] lemma Two_0_eq_1_eq_false : ¬(_0 = _1) :=
by contradiction

@[simp] lemma Two_1_eq_0_eq_false : ¬(_1 = _0) :=
by contradiction

-- TODO move to lean-tidy
@[applicable] definition decidable_true  : decidable true  := is_true  begin trivial end
@[applicable] definition decidable_false : decidable false := is_false ♯ 

@[tidy] meta def induction_Two : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(Two) := induction h >> skip | _ := failed end))

instance Two_decidable : decidable_eq Two := ♯

definition Two.choice {α : Sort u} (a b : α) : Two → α 
| _0 := a
| _1 := b

@[simp] lemma Two.choice_0 {α : Sort u} (a b : α) : Two.choice a b _0 = a := by refl
@[simp] lemma Two.choice_1 {α : Sort u} (a b : α) : Two.choice a b _1 = b := by refl

definition Two.split_choice {Z : Two → Sort v} (f : Z _0) (g : Z _1) : Π i : Two, Z i
| _0 := f
| _1 := g
definition Two.dependent_choice {α : Sort u} {Z : α → Sort v} {a b : α} (f : Z a) (g : Z b) : Π i : Two, Z (Two.choice a b i) 
| _0 := f
| _1 := g

