-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..tactics
import .Two
import data.quot
import data.equiv

namespace categories.util.finite

universes u v

-- FIXME rip out Finite in favour of whatever is in mathlib

class Finite (α : Type u) :=
  (cardinality : nat)
  (bijection : trunc (equiv α (fin cardinality))) -- TODO this should just assert the existence of a bijection

@[applicable] definition empty_exfalso (x : false) : empty := begin exfalso, trivial end
@[applicable] definition pempty_exfalso (x : false) : pempty := begin exfalso, trivial end
@[simp] lemma lt_zero_eq_false (n : ℕ) : n < 0 = false := ♯

-- TODO move to lean-tidy?
local attribute [applicable] quot.mk
local attribute [reducible] function.left_inverse function.right_inverse

instance empty_is_Finite : Finite empty := {
  cardinality := 0,
  bijection := by obviously,
} 
instance pempty_is_Finite : Finite pempty := {
  cardinality := 0,
  bijection := by obviously
}

definition decidable_via_isomorphism {α : Type u} {β : Type v} [dec : decidable_eq β] (iso : equiv α β) : decidable_eq α :=
begin
  tidy,
  have x := dec (iso.to_fun a) (iso.to_fun b),
  induction x with neq eq,
  exact is_false begin
                   intros eq,
                   have eq' := congr_arg iso.to_fun eq,
                   tidy,
                 end,
  exact is_true  begin 
                   have eq' := congr_arg iso.inv_fun eq,
                   repeat_at_least_once {rewrite equiv.left_inv at eq'},
                   exact eq',
                 end
end

definition Finite_has_decidable_eq {α : Type u} [fin : Finite α] : decidable_eq α := 
begin
  tidy,
  have p := fin.bijection,
  have p' := trunc.lift decidable_via_isomorphism _ p _,
  tidy,
end

attribute [instance] Finite_has_decidable_eq
-- PROJECT etc.
-- instance Finite_product {α β : Type} [Finite α] [Finite β] : Finite (α × β) := sorry

def empty_function           {α : Sort u} : empty → α := ♯
def empty_dependent_function {Z : empty → Sort u} : Π i : empty, Z i := ♯
def pempty_function           {α : Sort u} : pempty.{v} → α := ♯
def pempty_dependent_function {Z : pempty.{v} → Sort u} : Π i : pempty, Z i := ♯

open Two

def to_as_true {c : Prop} [h₁ : decidable c] (h₂ : c) : as_true c :=
cast (if_pos h₂).symm trivial
 
instance Two_is_Finite : Finite Two := {
  cardinality := 2,
  bijection := begin 
    apply quot.mk, 
    refine { 
      to_fun := λ n, match n with
                        | _0 := ⟨ 0, ♯ ⟩
                        | _1 := ⟨ 1, ♯ ⟩
                      end,
      inv_fun  := λ n, match n.1, to_as_true n.2 with
                        | 0, _ := _0
                        | 1, _ := _1 
                      end,
      ..
    } ; obviously end
 }

end categories.util.finite