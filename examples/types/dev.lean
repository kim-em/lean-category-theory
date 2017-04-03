-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...monoidal_categories.monoidal_category
import ...monoidal_categories.braided_monoidal_category
import .types

namespace tqft.categories.examples.types

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.monoidal_category
open tqft.categories.braided_monoidal_category

-- local attribute [pointwise] funext

-- @[unfoldable] definition TensorProductOfTypes : TensorProduct CategoryOfTypes :=
-- {
--   onObjects     := λ p, p.1 × p.2,
--   onMorphisms   := λ _ _ p q, (p.1 q.1, p.2 q.2),
--   identities    := ♯,
--   functoriality := ♮
-- }

-- local attribute [simp] id_locked_eq

structure IsomorphicTypes ( α β : Type ) :=
  ( morphism : α → β )
  ( inverse  : β → α )
  ( witness_1 : morphism ∘ inverse = id )
  ( witness_2 : inverse ∘ morphism = id )

open list
open tactic monad expr

meta def destruct_conjunctions : tactic unit :=
repeat (do
  l ← local_context,
  first $ l^.for (λ h, do
    ht ← infer_type h >>= whnf,
    match ht with
    | ``(and %%a %%b) := do
      n ← get_unused_name `h none,
      mk_mapp ``and.left [none, none, some h] >>= assertv n a,
      n ← get_unused_name `h none,
      mk_mapp ``and.right [none, none, some h] >>= assertv n b,
      clear h
    | _ := failed
    end))

meta def induction' ( h : expr ) : tactic ( list expr ) :=
  induction h >>= 

meta def induction_list : list expr → tactic unit
| nil       := skip
| (h :: hs) := induction h >> induction_list hs

meta def intros_induction : tactic unit := 
do h ← intros,
   induction_list h

definition test : IsomorphicTypes (((ℕ × ℕ) × ℕ)) (ℕ × (ℕ × ℕ)) :=
begin
    refine {
        morphism := λ t, (t.1.1, (t.1.2, t.2)),
        inverse  := _,
        witness_1 := _,
        witness_2 := _
    },
    intros,
    induction a with a1 a23,
    induction a23 with a2 a3,
    split,
    split,
    all_goals { try { apply funext, intros } },
    all_goals { try { simp } },
    all_goals { try { dsimp } },
    apply prod.rec,
    induction x with x1 x23,
    induction x23 with x2 x3,
    dsimp,
end

definition test' : Isomorphism CategoryOfTypes ((ℕ × ℕ) × ℕ) (ℕ × (ℕ × ℕ)) :=
begin
    refine {
        morphism := λ t, (t.1.1, (t.1.2, t.2)),
        inverse  := _,
        witness_1 := _,
        witness_2 := _
    },
    unfold_unfoldable,
    intros,
    induction a with a1 a23,
    induction a23 with a2 a3,
    split,
    split,
    all_goals { try { apply funext, intros } },
    all_goals { unfold CategoryOfTypes },
    all_goals { try { simp } },
    all_goals { try { dsimp } },
    apply pair_equality_3,
    apply pair_equality_3,
    induction x with x12 x3,
    induction x12 with x1 x2,
    dsimp,

end

-- definition AssociatorForTypes : Associator TensorProductOfTypes :=
-- begin
--     refine {
--         morphism := {
--             components := λ p t, (t.1.1, (t.1.2, t.2)),
--             naturality := ♮
--         },
--         inverse := _,
--         witness_1 := _,
--         witness_2 := _
--     },
--     blast,
--     split,
--     intros X Y f,
--     dsimp at X,
--     induction X with X12 X3,
--     induction X12 with X1 X2,
--     dsimp at Y,
--     induction Y with Y12 Y3,
--     induction Y12 with Y1 Y2,
--     dsimp at f,
    
-- end

end tqft.categories.examples.types