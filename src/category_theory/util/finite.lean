-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..isomorphism
import ..types

open categories.isomorphism
open categories.types

namespace categories.util.finite

class Finite ( α : Type ) :=
  ( cardinality : nat )
  ( bijection : Bijection α (fin cardinality) )

definition decidable_via_isomorphism { α β : Type } [ dec : decidable_eq β ] ( iso : Bijection α β ) : decidable_eq α :=
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

instance Finite_has_decidable_eq { α : Type } [ fin : Finite α ] : decidable_eq α := decidable_via_isomorphism fin.bijection

-- instance Finite_product { α β : Type } [ Finite α ] [ Finite β ] : Finite (α × β) := sorry

def {u} empty_function           { α : Sort u } : empty → α := ♯
def {u} empty_dependent_function { Z : empty → Sort u } : Π i : empty, Z i := ♯

-- FIXME why doesn't the VM have code for this?
@[applicable] lemma empty_exfalso (x : false) : empty := begin exfalso, trivial end

-- PROJECT improve automation here. We run into a problem that dsimp and unfold_projections just switch back and forth.
instance empty_is_Finite : Finite empty := {
  cardinality := 0,
  bijection := begin
                 unfold Bijection,
                 fsplit, 
                 unfold_projections, 
                 intros, 
                 automatic_induction, 
                 unfold_projections, 
                 intros, 
                 applicable,
                 automatic_induction,
                 apply funext,
                 intros,
                 automatic_induction,
                 apply funext,
                 intros,
                 unfold_projections_hypotheses,
                 automatic_induction,
              end
}

open Two

-- This is really lame!
instance Two_is_Finite : Finite Two := {
  cardinality := 2,
  bijection := {
    morphism := λ n, match n with
                       | _0 := ⟨ 0, ♯ ⟩
                       | _1 := ⟨ 1, ♯ ⟩
                     end,
    inverse  := λ n, match n with
                       | ⟨ 0, _ ⟩ := _0
                       | ⟨ 1, _ ⟩ := _1 
                       | _        := _0 -- FIXME we shouldn't have to do this!                   
                     end,
    witness_1 := begin
                   apply funext,
                   intros,
                   induction x, -- FIXME We need to be able to specify that induction on a new type (e.g. Two) should be allowed in tidy.
                   tidy,
                 end,
    witness_2 := begin
                   apply funext,
                   intros,
                   induction x,
                   cases is_lt,
                   unfold_projections,
                   dsimp,
                   unfold Two_is_Finite._match_2, -- FIXME auxiliary definitions created just a moment ago should get unfolded...
                   unfold Two_is_Finite._match_1,
                   trivial,
                   cases a,
                   unfold_projections,
                   dsimp,
                   unfold Two_is_Finite._match_2,
                   unfold Two_is_Finite._match_1,
                   trivial,
                   cases a_2
                 end
    }
  }

definition {u} Two.choice { α : Sort u } ( a b : α ) : Two → α 
| _0 := a
| _1 := b
definition {v} Two.split_choice { Z : Two → Sort v } ( f : Z _0 ) ( g : Z _1 ) : Π i : Two, Z i
| _0 := f
| _1 := g
definition {u v} Two.dependent_choice { α : Sort u } { Z : α → Sort v } { a b : α } ( f : Z a ) ( g : Z b ) : Π i : Two, Z (Two.choice a b i) 
| _0 := f
| _1 := g

end categories.util.finite