-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation
import .isomorphism

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.equivalence

structure Equivalence ( C D : Category ) :=
  ( functor : Functor C D )
  ( inverse : Functor D C )
  ( isomorphism_1 : NaturalIsomorphism (FunctorComposition functor inverse) (IdentityFunctor C) )
  ( isomorphism_2 : NaturalIsomorphism (FunctorComposition inverse functor) (IdentityFunctor D) )

definition {u v} Surjective { α : Type u } { β : Type v } ( f : α → β ) : Prop := nonempty { g : β → α // g ∘ f = id }
definition {u v} Injective  { α : Type u } { β : Type v } ( f : α → β ) : Prop := Π { X Y : α }, (f X = f Y) → (X = Y)

definition {u1 v1 u2 v2} Full     { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π ( X Y : C.Obj ), Surjective (@Functor.onMorphisms _ _ F X Y)
definition {u1 v1 u2 v2} Faithful { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π ( X Y : C.Obj ), Injective  (@Functor.onMorphisms _ _ F X Y)

definition {u1 v1 u2 v2} Embedding { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := (Full F) ∧ (Faithful F)

definition {u1 v1 u2 v2} EssentiallySurjective { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π d : D.Obj, Σ c : C.Obj, Isomorphism D (F c) d

-- PROJECT equivalences are fully faithful and essentially surjective
-- PROJECT iff

end tqft.categories.equivalence