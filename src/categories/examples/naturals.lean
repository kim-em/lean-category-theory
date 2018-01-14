-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import categories.natural_transformation

namespace categories.examples.naturals

open categories
open categories.functor

@[simp]
lemma nat_add_left_cancel_iff (a b : ℕ) : a + b = a ↔ b = 0 :=
@add_left_cancel_iff _ _ a b 0

@[simp]
lemma nat_add_right_cancel_iff (a b : ℕ) : a + b = b ↔ a = 0 :=
begin
  have h := @add_right_cancel_iff _ _ b a 0,
  simp at h,
  exact h
end

-- @[ematch]
-- lemma nat_add_associativity (a b c : ℕ) : nat.add (nat.add a b) c = nat.add a (nat.add b c) :=
-- begin
--   exact nat.add_assoc a b c
-- end
-- @[ematch]
-- lemma nat_add_commutativity (a b : ℕ) : nat.add a b = nat.add a b := ♮

-- FIXME This reducible is gross, but without it we can't see what NCategory.Hom is...
-- @[reducible] definition ℕCategory : Category :=
--   begin
--     refine {
--         Obj := unit,
--         Hom := λ _ _, ℕ,
--         identity := _, -- Notice we don't specify the identity here: `refine` works it out for us.
--         compose  := λ _ _ _ n m, n + m,

--         left_identity  := _,
--         right_identity := _,
--         associativity  := _
--     },
--     all_goals { blast }
--   end

-- -- @[simp] lemma ℕCategory.hom { X Y : ℕCategory.Obj } : ℕCategory.Hom X Y = ℕ := ♮

-- definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
--   { onObjects   := id,
--     onMorphisms := λ _ _ n, n + n, -- TODO this is ugly.
--     identities    := ♯,
--     functoriality := ♯
--   }

end categories.examples.naturals
