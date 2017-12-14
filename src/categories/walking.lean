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

@[simp] lemma Two_0_eq_1_eq_false : ¬(_0 = _1) :=
by contradiction

@[simp] lemma Two_1_eq_0_eq_false : ¬(_1 = _0) :=
by contradiction

@[applicable] definition decidable_true  : decidable true  := is_true  begin trivial end
@[applicable] definition decidable_false : decidable false := is_false ♯ 

instance Two_decidable : decidable_eq Two := ♯

instance : subsingleton empty :=
begin
tidy,
end

def {u} unit_or_empty_subsingleton {α : Type u} [decidable_eq α] {a b : α} : subsingleton (ite (a = b) unit empty) :=
begin
by_cases a = b,
rw h,
simp,
apply_instance,
rw if_neg h,
apply_instance,
end
def {u} unit_or_empty_subsingleton' {α : Type u} [decidable_eq α] {a : α} {Z : Type}: subsingleton (ite (a = a) unit Z) :=
begin
simp,
apply_instance,
end
attribute [instance] unit_or_empty_subsingleton
attribute [instance] unit_or_empty_subsingleton'
local attribute [applicable] subsingleton.elim

-- TODO automation? allow induction on booleans?
definition WalkingPair' : Category := {
  Obj := Two,
  Hom := λ X Y, if X = Y then unit else empty,
  identity       := ♯,
  compose        := begin tidy, simp at a, induction a, tidy, simp at a_1, induction a_1, tidy, simp at a_1, induction a_1, tidy,  end,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯,
}
definition WalkingPair : Category := {
  Obj := bool,
  Hom := λ X Y, if X = Y then unit else empty,
  identity       := ♯,
  compose        := begin tidy, induction X, any_goals { induction Y }, any_goals { induction Z }, tidy, induction a_1,induction a,induction a, induction a_1, end,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯,
}


definition Pair_functor { C : Category } ( α β : C.Obj ) : Functor WalkingPair C :=
{
  onObjects     := λ p, cond p α β,
  onMorphisms   := λ X Y f, begin induction X, any_goals { induction Y }, any_goals { simp }, exact C.identity β, induction f, induction f, exact C.identity α end,
  identities    := begin tidy, induction X, refl, refl, end,
  functoriality := begin tidy, induction X, any_goals {induction Y }, any_goals {induction Z}, any_goals { induction f }, any_goals { induction g }, tidy end
}

definition WalkingParallelPair : Category := {
  Obj := Two,
  Hom := begin intros, cases a, cases a_1, exact unit, exact bool, cases a_1, exact empty, exact unit, end,
  identity       := ♯,
  compose        := begin intros, induction X, any_goals { induction Y }, any_goals { induction Z }, tidy, exact a_1, exact a end,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition ParallelPair_functor { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) : Functor WalkingParallelPair C := 
{
  onObjects     := begin intros, cases a, exact α, exact β end,
  onMorphisms   := begin intros, cases X, cases Y, exact C.identity _, cases a, exact f, exact g, cases Y, cases a, cases a, exact C.identity _, end,
  identities    := ♯,
  functoriality := ♯
}

end categories.walking

