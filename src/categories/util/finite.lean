-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..tactics
import .Two

namespace categories.util.finite

universes u v

structure Bijection (U : Type u) (V : Type v) := -- TODO this should use equiv
  ( morphism : U → V )
  ( inverse  : V → U )
  ( witness_1 : ∀ u : U, inverse (morphism u) = u . tidy' )
  ( witness_2 : ∀ v : V, morphism (inverse v) = v . tidy' )

class Finite (α : Type u) :=
  ( cardinality : nat )
  ( bijection : Bijection α (fin cardinality) ) -- TODO this should just assert the existence of a bijection

@[applicable] definition empty_exfalso (x : false) : empty := begin exfalso, trivial end

-- PROJECT improve automation here. We run into a problem that dsimp and unfold_projections just switch back and forth.
instance empty_is_Finite : Finite empty := {
  cardinality := 0,
  bijection := begin
                 fsplit, 
                 intros,
                 induction a,
                 intros,
                 induction a,
                 apply empty_exfalso,
                 cases a_is_lt,
                 dsimp,
                 intros, 
                 induction u,
                 dsimp,
                 intros,
                 induction v,
                 cases v_is_lt,
              end
} 

definition decidable_via_isomorphism {α : Type u} {β : Type v} [ dec : decidable_eq β ] ( iso : Bijection α β ) : decidable_eq α :=
begin
  tidy,
  have x := dec (iso.morphism a) (iso.morphism b),
  induction x with neq eq,
  exact is_false begin
                   intros eq,
                   have eq' := congr_arg iso.morphism eq,
                   tidy,
                 end,
  exact is_true  begin 
                   have eq' := congr_arg iso.inverse eq,
                   repeat_at_least_once { rewrite Bijection.witness_1 at eq' },
                   exact eq',
                 end
end

definition Finite_has_decidable_eq {α : Type u} [fin : Finite α] : decidable_eq α := decidable_via_isomorphism fin.bijection
attribute [instance] Finite_has_decidable_eq
-- PROJECT etc.
-- instance Finite_product { α β : Type } [ Finite α ] [ Finite β ] : Finite (α × β) := sorry

def empty_function           {α : Sort u} : empty → α := ♯
def empty_dependent_function {Z : empty → Sort u} : Π i : empty, Z i := ♯

open Two

def to_as_true {c : Prop} [h₁ : decidable c] (h₂ : c) : as_true c :=
cast (if_pos h₂).symm trivial
 
open tactic

instance Two_is_Finite : Finite Two := {
  cardinality := 2,
  bijection := {
    morphism := λ n, match n with
                       | _0 := ⟨ 0, ♯ ⟩
                       | _1 := ⟨ 1, ♯ ⟩
                     end,
    inverse  := λ n, match n.1, to_as_true n.2 with
                       | 0, _ := _0
                       | 1, _ := _1 
                     end
    }
  }

definition Two.choice { α : Sort u } ( a b : α ) : Two → α 
| _0 := a
| _1 := b
definition Two.split_choice { Z : Two → Sort v } ( f : Z _0 ) ( g : Z _1 ) : Π i : Two, Z i
| _0 := f
| _1 := g
definition Two.dependent_choice { α : Sort u } { Z : α → Sort v } { a b : α } ( f : Z a ) ( g : Z b ) : Π i : Two, Z (Two.choice a b i) 
| _0 := f
| _1 := g

end categories.util.finite