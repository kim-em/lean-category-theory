-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.tactics
import categories.util.Two
import data.quot
import data.equiv
import data.fintype

namespace categories.util.finite

universes u v

-- class Finite (α : Type u) :=
--   (cardinality : nat)
--   (bijection : trunc (equiv α (fin cardinality))) 

-- local attribute [applicable] quot.mk
-- local attribute [reducible] function.left_inverse function.right_inverse

-- @[simp] lemma lt_zero_eq_false (n : ℕ) : n < 0 = false := by obviously'

-- instance : Finite empty := {
--   cardinality := 0,
--   bijection := by obviously',
-- } 

-- instance pempty_Finite : Finite pempty := {
--   cardinality := 0,
--   bijection := by obviously'
-- }

-- def to_as_true {c : Prop} [h₁ : decidable c] (h₂ : c) : as_true c :=
-- cast (if_pos h₂).symm trivial
 

-- open Two

-- instance Two_Finite : Finite Two := {
--   cardinality := 2,
--   bijection := begin 
--     apply quot.mk, 
--     refine { 
--       to_fun := λ n, match n with
--                         | _0 := ⟨ 0, by obviously' ⟩
--                         | _1 := ⟨ 1, by obviously' ⟩
--                       end,
--       inv_fun  := λ n, match n.1, to_as_true n.2 with
--                         | 0, _ := _0
--                         | 1, _ := _1 
--                       end,
--       ..
--     } ; obviously' end
--  }

-- instance  {α : Type u} [fin : Finite α] : decidable_eq α := 
-- begin
--   tidy,
--   have p := fin.bijection,
--   have p' := trunc.lift equiv.decidable_eq _ p,
--   tidy,
-- end

-- -- PROJECT etc.
-- instance Finite_product {α β : Type} [Finite α] [Finite β] : Finite (α × β) := sorry

end categories.util.finite