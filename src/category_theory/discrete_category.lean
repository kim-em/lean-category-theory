-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor

namespace categories

open categories.functor
open plift -- we first plift propositional equality to Type 0,
open ulift -- then ulift up to Type v

definition {u v} DiscreteCategory ( α : Type u ) : Category.{u v} :=
{
  Obj            := α,
  Hom            := λ X Y, ulift (plift (X = Y)),
  identity       := ♯,
  compose        := ♯,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition {u v} EmptyCategory := DiscreteCategory.{u v} (ulift empty)

definition {u1 v1 u2 v2} EmptyFunctor ( C : Category.{u2 v2} ) : Functor EmptyCategory.{u1 v1} C := ♯

@[simp] private lemma {u v} plift_rec_const { α : Type u } ( A A' : α ) { β : Type v } ( b : β ) : @plift.rec (A = A') (λ p, β) (λ p, b) = (λ p, b) :=
begin
  apply funext,
  intros,
  induction x,
  simp,
end
@[simp] private lemma {u v} ulift_rec_const { α : Type u } ( A A' : α ) { β : Type v } ( b : β ) : @ulift.rec (plift (A = A')) (λ p, β) (λ p, b) = (λ p, b) :=
begin
  apply funext,
  intros,
  induction x,
  simp,
end

definition {u1 v1 u2 v2} Functor.fromFunction { C : Category.{u1 v1} } { I : Type u2 } ( F : I → C.Obj ) : Functor (DiscreteCategory.{u2 v2} I) C := {
  onObjects     := F,
  onMorphisms   := by tidy,
  identities    := ♯,
  functoriality := ♯  
}

end categories
