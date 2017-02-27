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

@[reducible] definition ℕPreMonoidalCategory : PreMonoidalCategory :=
  { ℕCategory with
    tensor      := ℕTensorProduct,
    tensor_unit := ()
  }

-- Why can't it figure out there's a zero here?
definition ℕAssociator : Associator ℕPreMonoidalCategory :=
  { components := λ _, 0,
    naturality := sorry
  }

--definition ℕLaxMonoidalCategory : LaxMonoidalCategory :=
--  { ℕPreMonoidalCategory with
--    associator_transformation := ℕAssociator,
--    pentagon := sorry
--  }

end tqft.categories.examples.naturals
