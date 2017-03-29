-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ...natural_transformation
import ...monoidal_categories.monoidal_category

namespace tqft.categories.examples.naturals

open tqft.categories
open tqft.categories.functor
open tqft.categories.monoidal_category

@[simp]
lemma add_left_cancel_iff' (a b : ℕ) : a + b = a ↔ b = 0 :=
@add_left_cancel_iff _ _ a b 0

@[simp]
lemma add_right_cancel_iff' (a b : ℕ) : a + b = b ↔ a = 0 :=
begin
  note h := @add_right_cancel_iff _ _ b a 0,
  simp at h,
  exact h
end

-- FIXME This reducible is gross
@[reducible] definition ℕCategory : Category :=
  begin
    refine {
        Obj := unit,
        Hom := λ _ _, ℕ,
        identity := _,
        compose  := λ _ _ _ n m, n + m,

        left_identity  := _,
        right_identity := _,
        associativity  := _
    },
    all_goals { intros, try { simp } }
  end

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := (λ _ _ n, n + n),
    identities    := ♮,
    functoriality := ♮
  }

end tqft.categories.examples.naturals
