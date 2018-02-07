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

universes u₁ u₂ u₃ u₄

open Two

instance : subsingleton empty :=
begin
tidy,
end

def unit_or_empty_subsingleton {α : Type u₁} [decidable_eq α] {a b : α} : subsingleton (ite (a = b) unit empty) :=
begin
by_cases a = b,
rw h,
simp,
apply_instance,
rw if_neg h,
apply_instance,
end
-- TODO remove?
-- def unit_or_empty_subsingleton' {α : Type u₁} [decidable_eq α] {a : α} {Z : Type}: subsingleton (ite (a = a) unit Z) :=
-- begin
-- simp,
-- apply_instance,
-- end
attribute [instance] unit_or_empty_subsingleton
-- attribute [instance] unit_or_empty_subsingleton'
local attribute [applicable] subsingleton.elim


-- FIXME: see as https://github.com/leanprover/lean/issues/1915
meta def simp_at_each : tactic unit :=
do l ← tactic.local_context,
  (s, u) ← tactic.mk_simp_set ff [] [],
  tactic.interactive.simp_core_aux {} tactic.failed s u l ff

local attribute [tidy] simp_at_each

inductive {u} pempty : Type u

open tactic
@[tidy] meta def induction_pempty : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(pempty) := induction h >> skip | _ := failed end))


meta def induction' (e :expr) := tactic.interactive.induction (none, to_pexpr e) none [] none

definition foo (f : ite (_0 = _0) punit pempty) : punit.star = f := begin
induction f,
refl,
end

meta def induction_only : tactic unit :=
do l ← local_context,
   match l with 
   | [e] := do t ← infer_type e,
               t ← whnf t,
               match t with
               | `(punit) := induction' e
               | _ := skip
               end
   | _   := failed
   end

definition foo' (f : ite (_0 = _0) punit pempty) : punit.star = f :=
begin
induction_only,
refl
end


definition WalkingPair : Category.{u₁ u₂} := {
  Obj := Two,
  Hom := λ X Y, if X = Y then punit else pempty,
  identity       := by tidy, 
  compose        := by tidy,
  left_identity := begin dsimp', intros, induction_Two, dsimp', 
                    --  do l ← local_context, 
                    --     tactic.trace l.head, 
                    --     t ← infer_type l.head, 
                    --     tactic.trace t, 
                    --     t' <- whnf t, 
                    --     tactic.trace t', 
                    --     match t' with 
                    --       | `(punit) := tactic.trace "foo" 
                    --       | _ := tactic.trace "bar" 
                    --     end,
                    --  induction f,
                      do l ← local_context, 
                      h ← pure l.head,
                        induction' h, skip,
                       induction f,
                      admit
                    end,
  right_identity := sorry,
  associativity := sorry
}

definition Pair_functor { C : Category.{u₃ u₄} } ( α β : C.Obj ) : Functor.{u₁ u₂ u₃ u₄} WalkingPair C :=
{
  onObjects     := λ p, cond p.down α β,
  onMorphisms   := λ X Y f, begin tidy, induction X, any_goals { induction Y }, any_goals { simp }, exact C.identity β, induction f, induction f, exact C.identity α end,
  identities    := begin tidy, induction X, refl, refl, end,
  functoriality := begin tidy, induction X, any_goals { induction Y }, any_goals { induction Z }, any_goals { induction f }, any_goals { induction g }, tidy end
}
#check punit
definition WalkingParallelPair : Category.{u₁ u₂} := {
  Obj := Two,
  Hom := (begin intros, cases a, cases a_1, exact punit, exact ulift bool, cases a_1, exact empty, exact punit, end),
  identity       := ♯,
  compose        := begin intros, any_goals { induction X }, any_goals { induction Y }, any_goals { induction Z }, tidy, exact a_1, exact a end
}

definition ParallelPair_functor { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) : Functor WalkingParallelPair C := 
{
  onObjects     := begin intros, cases a, exact α, exact β end,
  onMorphisms   := begin intros, cases X, cases Y, exact C.identity _, cases a, exact f, exact g, cases Y, cases a, cases a, exact C.identity _, end
}

end categories.walking

