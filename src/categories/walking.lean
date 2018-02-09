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

def {u} unit_or_empty_subsingleton {α : Type u} [decidable_eq α] {a b : α} : subsingleton (ite (a = b) unit empty) :=
begin
by_cases a = b,
rw h,
simp,
apply_instance,
rw if_neg h,
apply_instance,
end
-- TODO remove?
-- def {u} unit_or_empty_subsingleton' {α : Type u} [decidable_eq α] {a : α} {Z : Type}: subsingleton (ite (a = a) unit Z) :=
-- begin
-- simp,
-- apply_instance,
-- end
attribute [instance] unit_or_empty_subsingleton
-- attribute [instance] unit_or_empty_subsingleton'
local attribute [applicable] subsingleton.elim


definition WalkingPair : Category.{u₁ u₂} := {
  Obj := Two,
  Hom := λ X Y, if X = Y then punit else pempty,
  identity       := by tidy, 
  compose        := by tidy,
}

local attribute [applicable] Category.identity
definition Pair_functor {C : Category.{u₃ u₄}} (α β : C.Obj) : Functor.{u₁ u₂ u₃ u₄} WalkingPair C :=
{
  onObjects     := λ p, p.choice α β,
  onMorphisms   := by tidy
}

definition WalkingParallelPair : Category.{u₁ u₂} := {
  Obj := Two,
  Hom := begin
           intros X Y,
           induction X,
           {induction Y, exact punit, exact Two},
           {induction Y, exact pempty, exact punit}
         end,
  identity       := by tidy,
  compose        := begin
                      intros X Y Z f g, induction X, any_goals {induction Y}, any_goals {induction Z}, any_goals {dsimp at *}, 
                      exact punit.star, exact g, exact punit.star, exact f, induction f, exact punit.star, induction g, exact punit.star
                    end
}

-- this style is obscene. FIXME learn to use match statements  (or rather, to automatically unfold them)
definition ParallelPair_functor {C : Category} {α β : C.Obj} (f g : C.Hom α β) : Functor WalkingParallelPair C := 
{
  onObjects     := begin intros X, induction X, exact α, exact β end,
  onMorphisms   := begin
                     intros,
                     induction X,
                     {induction Y,
                       {exact C.identity α},
                       {induction a, exact f, exact g}},
                     {induction Y,
                       {induction a},
                       {exact C.identity β}}
                   end
}

end categories.walking

