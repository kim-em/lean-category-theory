-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..natural_transformation
import ..monoidal_categories.monoidal_category

namespace tqft.categories.examples.naturals

open tqft.categories
open tqft.categories.functor
open tqft.categories.monoidal_category

@[simp]
lemma add_left_cancel_iff' (a b : ℕ) : a + b = a ↔ b = 0 :=
@add_left_cancel_iff _ _ a b 0

@[simp]
lemma add_right_cancel_iff' (a b : ℕ) : a + b = b ↔ a = 0 :=
begin
  note h := @add_right_cancel_iff _ _ b a 0,
  simp at h,
  exact h
end

@[reducible] definition ℕCategory : Category :=
  begin
    refine {
        Obj := unit,
        Hom := λ _ _, ℕ,
        identity := _,
        compose  := λ _ _ _ n m, n + m,

        left_identity  := _,
        right_identity := _,
        associativity  := _
    },
    all_goals { intros, try { simp } }
  end

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := (λ _ _ n, n + n),
    identities    := ♮,
    functoriality := ♮
  }

@[reducible] definition ℕTensorProduct : TensorProduct ℕCategory :=
  { onObjects     := prod.fst,
    onMorphisms   := λ _ _ n, n^.fst + n^.snd,
    identities    := ♮,
    functoriality := ♮
  }

-- TODO What follows involves a lot of boring natural transformations
-- Can we construct them automatically?
definition ℕMonoidalCategory : MonoidalCategory :=
 begin
 refine 
   { ℕCategory with
   tensor                    := ℕTensorProduct,
   tensor_unit               := (),
   associator_transformation := { components := λ _, 0, naturality := ♮ },
   left_unitor               := { components := λ _, 0, naturality := ♮ },
   right_unitor              := { components := λ _, 0, naturality := ♮ },

   associator_is_isomorphism := {
     inverse := { components := _, naturality := _ },
     witness_1 := _,
     witness_2 := _
   },
  --  associator_is_isomorphism := {
  --    inverse := { components := λ _, 0, naturality := ♮ },
  --    witness_1 := ♮,
  --    witness_2 := ♮
  --  },
   left_unitor_is_isomorphism := {
     inverse := { components := λ _, 0, naturality := ♮ },
     witness_1 := ♮,
     witness_2 := ♮
   },
   right_unitor_is_isomorphism := {
     inverse := { components := λ _, 0, naturality := ♮ },
     witness_1 := ♮,
     witness_2 := ♮
   },
   pentagon := ♮,
   triangle := ♮
 },
  all_goals { blast },
  -- all_goals { induction X },
  -- all_goals { induction fst },
  -- all_goals { induction snd },
  -- all_goals { induction fst_1 },
  -- all_goals { induction snd_1 }
 end

end tqft.categories.examples.naturals
