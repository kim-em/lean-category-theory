-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .naturals

namespace tqft.categories.examples.naturals

open tqft.categories
open tqft.categories.functor
open tqft.categories.monoidal_category

@[unfoldable] definition ℕTensorProduct : TensorProduct ℕCategory :=
  { onObjects     := prod.fst,
    onMorphisms   := λ _ _ n, n^.fst + n^.snd,
    identities    := ♮,
    functoriality := ♯
  }

-- TODO What follows involves a lot of boring natural transformations
-- Can we construct them automatically?
definition ℕMonoidalCategory : MonoidalStructure ℕCategory :=
 begin
 refine 
   { 
   tensor                    := ℕTensorProduct,
   tensor_unit               := (),
   associator_transformation := { components := λ _, 0, naturality := ♯ },
   left_unitor               := { components := λ _, 0, naturality := ♯ },
   right_unitor              := { components := λ _, 0, naturality := ♯ },

  -- -- I'd really like this to work, so we don't need to construct boring inverses by hand.
  --  associator_is_isomorphism := {
  --    inverse := { components := _, naturality := _ },
  --    witness_1 := _,
  --    witness_2 := _
  --  },
   associator_is_isomorphism := {
     inverse := { components := λ _, 0, naturality := ♯ },
     witness_1 := ♮,
     witness_2 := ♮
   },
   left_unitor_is_isomorphism := {
     inverse := { components := λ _, 0, naturality := ♯ },
     witness_1 := ♮,
     witness_2 := ♮
   },
   right_unitor_is_isomorphism := {
     inverse := { components := λ _, 0, naturality := ♯ },
     witness_1 := ♮,
     witness_2 := ♮
   },
   pentagon := ♯,
   triangle := ♯
 },
  all_goals { blast },
  -- all_goals { induction X },
  -- all_goals { induction fst },
  -- all_goals { induction snd },
  -- all_goals { induction fst_1 },
  -- all_goals { induction snd_1 }
 end

end tqft.categories.examples.naturals
