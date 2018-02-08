-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import categories.natural_transformation
import init.data.nat.lemmas
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

@[simp] private lemma zero_add_iff (a b : ℕ) : ((nat.add b a) = a) ↔ (b = 0) := 
begin
tidy,
{
have q : nat.add b a = a + b, by tidy,
rw q at a_1,
have p : a = a + 0, by simp,
rw p at a_1,
have r : a + 0 + b = a + b, by simp,
rw r at a_1,
exact nat.add_left_cancel a_1
},
{ rw a_1, simp }
end

-- PROJECT This reducible is gross, but without it we can't see what NCategory.Hom is...
@[reducible] definition ℕCategory : Category :=
  {
        Obj := unit,
        Hom := λ _ _, ℕ,
        identity := _,
        compose  := λ _ _ _ n m, n + m,
  }  

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := λ _ _ n, n + n, -- PROJECT this is ugly: why can't we write `2 * n`
  }

end categories.examples.naturals
