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

-- definition WalkingPair : Graph := {
--   Obj := Two,
--   Hom := λ X Y, empty
-- }

@[simp] lemma Two_0_eq_1_eq_false : ¬(_0 = _1) :=
by contradiction

@[simp] lemma Two_1_eq_0_eq_false : ¬(_1 = _0) :=
by contradiction

@[applicable] definition decidable_true  : decidable true  := is_true  begin trivial end
@[applicable] definition decidable_false : decidable false := is_false ♯ 

instance Two_decidable : decidable_eq Two := ♯

-- TODO automation? allow induction on booleans?
definition WalkingPair : Category := {
  Obj := Two,
  Hom := λ X Y, if X = Y then unit else empty,
  identity       := begin tidy, end,
  compose        := begin tidy, simp at a, induction a, tidy, simp at a_1, induction a_1, tidy, simp at a_1, induction a_1, tidy,  end,
  left_identity  := begin intros, dsimp', tidy {trace_result:=tt}, induction f, intros, induction X, any_goals { induction Y }, any_goals { induction f }, refl, refl end,
  right_identity := sorry,
  associativity  := sorry,
}

-- TODO Which is more usable? WalkingPair : Graph or WalkingPair : Category?

-- definition WalkingParallelPair : Graph := {
--   Obj := Two,
--   Hom := λ X Y, match X, Y with 
--                   | _0, _1 := Two
--                   | _,  _  := empty
--                 end
-- }



definition Pair_functor { C : Category } ( α β : C.Obj ) : Functor WalkingPair C :=
{
  onObjects     := λ p, cond p α β,
  onMorphisms   := λ X Y f, begin induction X, any_goals { induction Y }, any_goals { simp }, exact C.identity β, induction f, induction f, exact C.identity α end,
  identities    := begin tidy, induction X, refl, refl, end,
  functoriality := begin tidy, induction X, any_goals {induction Y }, any_goals {induction Z}, any_goals { induction f }, any_goals { induction g }, tidy end
}


-- definition ParallelPair_homomorphism { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) : GraphHomomorphism WalkingParallelPair C.graph := {
--   onObjects   := λ X, match X with
--                        | _0 := α
--                        | _1 := β
--                      end,
--   onMorphisms := λ X Y e, match X, Y, e with
--                            | _0, _1, _0 := f
--                            | _0, _1, _1 := g
--                          end
-- }

-- definition ParallelPair_functor { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) := Functor.from_GraphHomomorphism (ParallelPair_homomorphism f g)

end categories.walking

