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

definition is_Equivalence { C D : Category } ( F : Functor C D ) := { e : Equivalence C D // e.functor = F }

definition Equivalence.reverse { C D : Category } ( e : Equivalence C D ) : Equivalence D C :=
{
  functor := e.inverse,
  inverse := e.functor,
  isomorphism_1 := e.isomorphism_2,
  isomorphism_2 := e.isomorphism_1
}

definition {u v} Surjective { α : Type u } { β : Type v } ( f : α → β ) := { g : β → α // g ∘ f = id } -- This is the constructive version!
definition {u v} Injective  { α : Type u } { β : Type v } ( f : α → β ) := Π { X Y : α }, (f X = f Y) → (X = Y)

definition {u1 v1 u2 v2} Full     { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π ( X Y : C.Obj ), Surjective (@Functor.onMorphisms _ _ F X Y)
definition {u1 v1 u2 v2} Faithful { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π ( X Y : C.Obj ), Injective  (@Functor.onMorphisms _ _ F X Y)

definition {u1 v1 u2 v2} Embedding { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := (Full F) × plift (Faithful F)

definition {u1 v1 u2 v2} EssentiallySurjective { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π d : D.Obj, Σ c : C.Obj, Isomorphism D (F c) d

lemma Equivalences_are_EssentiallySurjective { C D : Category } ( e : Equivalence C D ) : EssentiallySurjective (e.functor) :=
  λ Y : D.Obj, ⟨ e.inverse Y, e.isomorphism_2.components Y ⟩
lemma Equivalences_are_Full { C D : Category } ( e : Equivalence C D ) : Full (e.functor) :=
  λ X Y : C.Obj,
      ⟨ λ f : D.Hom (e.functor X) (e.functor Y),
          C.compose (C.compose (e.isomorphism_1.inverse.components X) (e.inverse.onMorphisms f)) (e.isomorphism_1.morphism.components Y),
        begin 
          -- Now we have to prove that really was a pre-image; it's not pretty.
          blast, 
          assert p : ((e.inverse).onMorphisms ((e.functor).onMorphisms x)) = (FunctorComposition e.functor e.inverse).onMorphisms x, blast,
          rewrite p,
          erewrite - e.isomorphism_1.inverse.naturality,
          blast,
          rewrite C.associativity,
          erewrite e.isomorphism_1.componentwise_witness_2,
          blast
        end
    ⟩

-- PROJECT finish this
-- lemma Equivalences_are_Faithful { C D : Category } ( e : Equivalence C D ) : Faithful (e.functor) := sorry

-- PROJECT finish this
-- lemma FullyFaithfulEssentiallySurjective_Functors_are_Equivalences
--   { C D : Category } 
--   ( F : Functor C D ) 
--   ( full : Full F ) 
--   ( faithful : Faithful F ) 
--   ( essentially_surjective : EssentiallySurjective F ) : is_Equivalence F :=
--   ⟨
--     {
--       functor := F,
--       inverse := {
--         onObjects     := λ X : D.Obj, (essentially_surjective X).1,
--         onMorphisms   := λ X Y f,
--                            (full (essentially_surjective X).1 (essentially_surjective Y).1).val
--                              (D.compose (D.compose (
--                                (essentially_surjective X).2.morphism)
--                                f
--                               ) (
--                                (essentially_surjective Y).2.inverse)
--                               ),
--         identities    := sorry,
--         functoriality := sorry
--       },
--       isomorphism_1 := sorry, -- Construct these using NaturalIsomorphism.from_components
--       isomorphism_2 := sorry
--     },
--     ♮
--   ⟩

end tqft.categories.equivalence