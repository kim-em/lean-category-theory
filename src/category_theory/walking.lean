-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .discrete_category
import .path_category
import .util.finite

open categories
open categories.graphs
open categories.functor
open categories.util.finite

namespace categories.walking

open Two

definition WalkingPair : Graph := {
  Obj := Two,
  Hom := λ X Y, empty
}
-- PROJECT grah, what a pain!
-- definition WalkingPair' : Category := {
--   Obj := Two,
--   Hom := λ X Y, match X, Y with
--                   | _0, _0 := unit
--                   | _1, _1 := unit
--                   | _,  _  := empty
--                 end,
--   identity := begin tidy, induction X, unfold WalkingPair'._match_1, tidy, unfold WalkingPair'._match_1, tidy end,
--   compose := begin tidy, induction X, induction Y, induction Z, end,
--   left_identities := sorry,
--   right_identities := sorry,
--   associativity := sorry,
-- }

@[simp] lemma Two_0_eq_1_eq_false : ¬(_0 = _1) :=
by contradiction

@[simp] lemma Two_1_eq_0_eq_false : ¬(_1 = _0) :=
by contradiction

@[applicable] lemma decidable_true  : decidable true  := is_true  begin trivial end
@[applicable] lemma decidable_false : decidable false := is_false ♯ 

instance Two_decidable : decidable_eq Two := ♯

-- lemma ff_eq_ff : (ff = ff) = true := by simp

-- definition WalkingPair' : Category := {
--   Obj := bool,
--   Hom := λ X Y, if X = Y then unit else empty,
--   identity       := begin intros, induction X, any_goals { simp }, apply unit.star, apply unit.star end, -- tidy automates this, but I think I need a standalone example
--   compose        := begin intros, induction X, any_goals { induction Y }, any_goals { induction Z }, any_goals { simp at * }, any_goals { apply unit.star }, induction a_1, induction a, induction a, induction a_1, end,
--   left_identity  := begin tidy, rewrite ff_eq_ff at f, end,  -- FIXME how am I meant to do this?
--   right_identity := sorry,
--   associativity  := sorry,
-- }

definition WalkingParallelPair : Graph := {
  Obj := Two,
  Hom := λ X Y, match X, Y with 
                  | _0, _1 := Two
                  | _,  _  := empty
                end
}

definition Pair_homomorphism { C : Category } ( α β : C.Obj ) : GraphHomomorphism WalkingPair C.graph := {
  onObjects   := λ X, match X with
                       | _0 := α
                       | _1 := β
                      end,
  onMorphisms := λ X Y e, match X, Y, e with end
}

definition Pair_functor { C : Category } ( α β : C.Obj ) := Functor.from_GraphHomomorphism (Pair_homomorphism α β)

definition ParallelPair_homomorphism { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) : GraphHomomorphism WalkingParallelPair C.graph := {
  onObjects   := λ X, match X with
                       | _0 := α
                       | _1 := β
                     end,
  onMorphisms := λ X Y e, match X, Y, e with
                           | _0, _1, _0 := f
                           | _0, _1, _1 := g
                         end
}

definition ParallelPair_functor { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) := Functor.from_GraphHomomorphism (ParallelPair_homomorphism f g)

end categories.walking

