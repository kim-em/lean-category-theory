-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..natural_transformation
import ..monoidal_categories.monoidal_category

namespace tqft.categories.examples.naturals

open tqft.categories
open tqft.categories.functor
open tqft.categories.monoidal_category

-- Huh. Using nat.add rather than the notation makes life much more
-- difficult.
@[reducible] definition ℕCategory : Category :=
  {
    Obj := unit,
    Hom := λ _ _, ℕ,
    identity := λ _, 0,
    compose  := λ _ _ _ n m, n + m,

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
  }

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

-- What follows involves a lot of natural transformations than are
-- really the same thing (at least for the unitors). Can we get lean
-- to recognise this?
definition ℕMonoidalCategory : MonoidalCategory :=
 { ℕCategory with
   tensor                    := ℕTensorProduct,
   tensor_unit               := (),
   associator_transformation := { components := λ _, 0, naturality := ♮ },
  --  left_unitor               := { components := λ _, 0, naturality := ♮ },
  --  right_unitor              := { components := λ _, 0, naturality := ♮ },

   associator_is_isomorphism := {
     inverse := { components := λ _, 0, naturality := ♮ },
     witness_1 := ♮,
     witness_2 := ♮
   },
  --  left_unitor_is_isomorphism := {
  --    inverse := { components := λ _, 0, naturality := ♮ },
  --    witness_1 := ♮,
  --    witness_2 := ♮
  --  },
  --  right_unitor_is_isomorphism := {
  --    inverse := { components := λ _, 0, naturality := ♮ },
  --    witness_1 := ♮,
  --    witness_2 := ♮
  --  },

   pentagon := ♮
  --  triangle := ♮
 }

end tqft.categories.examples.naturals
