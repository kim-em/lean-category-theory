-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..functor
import ..natural_transformation
import ..products
import ..monoidal_category

namespace tqft.categories.examples.naturals

open tqft.categories
open tqft.categories.functor
open tqft.categories.monoidal_category

@[reducible] definition ℕCategory : Category :=
  {
    Obj := unit,
    Hom := λ _ _, ℕ,
    identity := λ _, 0,
    compose  := λ _ _ _, nat.add,

    left_identity  := begin blast, apply nat.zero_add end,
    right_identity := ♮,
    associativity  := begin blast, apply nat.add_assoc end
  }    

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := (λ _ _ n, nat.add n n),
    identities    := ♮,
    functoriality := begin blast, exact sorry end
  }

definition ℕTensorProduct : Functor (ℕCategory × ℕCategory) ℕCategory :=
  { onObjects     := prod.fst,
    onMorphisms   := λ _ _ n, n^.fst + n^.snd,
    identities    := ♮,
    functoriality := sorry
  }

def ℕLaxMonoidalCategory : LaxMonoidalCategory :=
  { ℕCategory with
    tensor       := ℕTensorProduct,
    tensor_unit  := (),
    associator   := λ _ _ _, Category.identity ℕCategory (),
    interchange  := sorry -- should be trivial, but how?
  }

end tqft.categories.examples.naturals
