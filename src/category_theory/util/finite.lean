-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..isomorphism
import ..types

open categories.isomorphism
open categories.types

namespace categories.util.finite

class Finite ( α : Type ) :=
  ( n : nat )
  ( bijection : Isomorphism CategoryOfTypes α (fin n) )

def {u} empty_function           { α : Sort u } : empty → α := ♯
def {u} empty_dependent_function { Z : empty → Sort u } : Π i : empty, Z i := ♯

-- TODO improve automation here
instance empty_is_Finite : Finite empty := {
  n := 0,
  bijection := begin
                 fsplit, 
                 unfold_projections, 
                 intros, 
                 induction a, 
                 unfold_projections, 
                 intros, 
                 induction a, 
                 exfalso, cases is_lt,
                 apply funext,
                 intros,
                 induction x,
                 apply funext,
                 intros,
                 induction x,
                 exfalso, cases is_lt,
              end
}

inductive Two : Type
| _0 : Two
| _1 : Two

open Two

set_option pp.all true
-- This is really lame!
instance Two_is_Finite : Finite Two := {
  n := 2,
  bijection := {
    morphism := λ n, match n with
                       | _0 := ⟨ 0, ♯ ⟩
                       | _1 := ⟨ 1, ♯ ⟩
                     end,
    inverse  := λ n, match n with
                       | ⟨ 0, _ ⟩ := _0
                       | ⟨ 1, _ ⟩ := _1 
                       | _        := _0 -- TODO we shouldn't have to do this!                   
                     end,
    witness_1 := begin
                   apply funext,
                   intros,
                   induction x, -- TODO We need to be able to specify that induction on a new type (e.g. Two) should be allowed in tidy.
                   tidy,
                 end,
    witness_2 := begin
                   apply funext,
                   intros,
                   induction x,
                   cases is_lt,
                   unfold_projections,
                   dsimp,
                   unfold Two_is_Finite._match_2, -- TODO auxiliary definitions created just a moment ago should get unfolded...
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