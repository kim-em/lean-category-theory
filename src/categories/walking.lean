-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .discrete_category
import .util.finite

open categories
open categories.functor
open categories.util.finite

namespace categories.walking

universes u₁ u₂

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

open Two

definition WalkingPair : category Two := {
  Hom := λ X Y, if X = Y then punit else pempty,
  identity       := by tidy, 
  compose        := by tidy,
}

local attribute [applicable] category.identity

variable {C : Type u₁}
variable [category C]

set_option pp.all true
definition Pair_functor (α β : C) : @Functor Two WalkingPair C _ := {
  onObjects     := λ p, p.choice α β,
  onMorphisms   := λ X Y f, match X, Y, f with
                            | _0, _0, _ := 𝟙 α
                            | _1, _1, _ := 𝟙 β
                            end,
  functoriality := begin
                     tidy, 
                     all_goals { induction f }, 
                     all_goals { induction g }, 
                     all_goals { dunfold Pair_functor._match_1 }, 
                     erw category.left_identity, -- FIXME
                     erw category.left_identity, 
                   end
}

definition WalkingParallelPair : category Two := {
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
definition ParallelPair_functor {α β : C} (f g : Hom α β) : @Functor Two WalkingParallelPair C _ := 
{
  onObjects     := begin intros X, induction X, exact α, exact β end,
  onMorphisms   := begin
                     intros,
                     induction X,
                     {induction Y,
                       {exact 𝟙 α},
                       {induction a, exact f, exact g}},
                     {induction Y,
                       {induction a},
                       {exact 𝟙 β}}
                   end,
  functoriality := begin tidy, any_goals { induction f_1 }, any_goals { induction g_1 },  end
}

end categories.walking

