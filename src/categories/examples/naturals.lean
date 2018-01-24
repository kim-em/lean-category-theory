-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import categories.natural_transformation

namespace categories.examples.naturals

open categories
open categories.functor

@[applicable] private lemma add_zero (a b) (p : b = 0) : (a + b = a) := 
begin
rw p,
simp
end
@[simp] private lemma zero_add (a : ℕ) : (nat.add 0 a) = a := 
begin
-- this is ridiculous
induction a,
refl,
unfold nat.add,
rw a_ih,
end

-- PROJECT This reducible is gross, but without it we can't see what NCategory.Hom is...
@[reducible] definition ℕCategory : Category :=
  {
        Obj := unit,
        Hom := λ _ _, ℕ,
        identity := _, -- Notice we don't specify the identity here!
        compose  := λ _ _ _ n m, n + m
  }  

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := λ _ _ n, n + n, -- PROJECT this is ugly: why can't we write `2 * n`
    identities    := ♯,
    functoriality := ♯
  }

end categories.examples.naturals
