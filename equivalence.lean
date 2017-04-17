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

structure {u1 v1 u2 v2} Equivalence ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) :=
  ( functor : Functor C D )
  ( inverse : Functor D C )
  ( isomorphism_1 : NaturalIsomorphism (FunctorComposition functor inverse) (IdentityFunctor C) )
  ( isomorphism_2 : NaturalIsomorphism (FunctorComposition inverse functor) (IdentityFunctor D) )

definition {u1 v1 u2 v2} is_Equivalence { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := { e : Equivalence C D // e.functor = F }

definition {u1 v1 u2 v2} Equivalence.reverse { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( e : Equivalence C D ) : Equivalence D C :=
{
  functor := e.inverse,
  inverse := e.functor,
  isomorphism_1 := e.isomorphism_2,
  isomorphism_2 := e.isomorphism_1
}

structure {u1 v1 u2 v2} Full     { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( preimage : ∀ { X Y : C.Obj } ( f : D.Hom (F X) (F Y) ), C.Hom X Y )
  ( witness  : ∀ { X Y : C.Obj } ( f : D.Hom (F X) (F Y) ), F.onMorphisms (preimage f) = f )

attribute [pointwise] Full.preimage
attribute [simp,ematch] Full.witness

structure {u1 v1 u2 v2} Faithful { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( injectivity : ∀ { X Y : C.Obj } ( f g : C.Hom X Y ) ( p : F.onMorphisms f = F.onMorphisms g ), f = g )

attribute [pointwise] Faithful.injectivity

definition {u1 v1 u2 v2} Embedding { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := (Full F) × (Faithful F)

definition {u1 v1 u2 v2} EssentiallySurjective { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π d : D.Obj, Σ c : C.Obj, Isomorphism D (F c) d

lemma Equivalences_are_EssentiallySurjective { C D : Category } ( e : Equivalence C D ) : EssentiallySurjective (e.functor) :=
  λ Y : D.Obj, ⟨ e.inverse Y, e.isomorphism_2.components Y ⟩

-- These is an annoying hack, because I can't simplify hypotheses automatically. FIXME
lemma {u1 v1} IdentityFunctor_is_identity { C : Category.{u1 v1} } { X Y : C.Obj } ( f : C.Hom X Y ) : (IdentityFunctor C).onMorphisms f = f := ♯
lemma {u1 v1 u2 v2 u3 v3} FunctorComposition_is_composition 
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  { F : Functor C D }
  { G : Functor D E }
  { X Y : C.Obj }
  { f : C.Hom X Y } :
  (FunctorComposition F G).onMorphisms f = G.onMorphisms (F.onMorphisms f) := ♯

private definition {u1 v1 u2 v2} preimage
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( e : Equivalence C D )
  ( X Y : C.Obj )
  ( h : D.Hom (e.functor X) (e.functor Y) ) :=
  C.compose (C.compose (e.isomorphism_1.inverse.components X) (e.inverse.onMorphisms h)) (e.isomorphism_1.morphism.components Y)

private lemma {u1 v1 u2 v2} preimage_is_retraction
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( e : Equivalence C D )
  ( X Y : C.Obj )
  ( f : C.Hom X Y ) :
  preimage e X Y (e.functor.onMorphisms f) = f :=
  e.isomorphism_1.naturality_1 f

private lemma {u v} sections_are_injective
  { A : Type u } { B : Type v }
  ( f : A → B ) ( g : B → A )
  ( f_section_of_g : ∀ (a : A), g (f a) = a )
  ( a b : A )
  ( H : f a = f b ) :
  a = b :=
    calc
      a   = g (f a) : eq.symm (f_section_of_g a)
      ... = g (f b) : congr_arg g H
      ... = b       : f_section_of_g b

lemma {u1 v1 u2 v2} Equivalences_are_Faithful { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( e : Equivalence C D ) : Faithful (e.functor) := {
  injectivity :=
    λ {X Y : C.Obj} (f g : C.Hom X Y),
      sections_are_injective e.functor.onMorphisms (preimage e X Y) (preimage_is_retraction e X Y) f g
}

private lemma {u1 v1 u2 v2} preimage_lemma { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( e : Equivalence C D ) ( X Y : C.Obj ) ( h : D.Hom (e.functor X) (e.functor Y) ) : (e.inverse).onMorphisms ((e.functor).onMorphisms (preimage e X Y h)) = (e.inverse).onMorphisms h :=
begin
  pose p := e.isomorphism_1.naturality_2 (preimage e X Y h),
  rewrite FunctorComposition_is_composition at p,
  rewrite (eq.symm p),
  unfold_unfoldable,
  repeat { rewrite - C.associativity },
  erewrite e.isomorphism_1.componentwise_witness_1,
  repeat { rewrite C.associativity },
  erewrite e.isomorphism_1.componentwise_witness_1,
  erewrite C.right_identity,
  erewrite C.left_identity
end

-- FIXME this is lame.
meta def rewrite_once : tactic unit :=
do r ← tactic.to_expr `(preimage_lemma e X Y h),
   tactic.rewrite_core semireducible tt tt (occurrences.pos [2]) tt r


lemma {u1 v1 u2 v2} Equivalences_are_Full { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( e : Equivalence C D ) : Full (e.functor) :=
  {
    preimage := preimage e,
    witness := 
        begin 
          intros X Y h,
          apply (Equivalences_are_Faithful e.reverse).injectivity,
          unfold_unfoldable,
          -- erewrite - (preimage_lemma e X Y h),
          rewrite_once,
          unfold_unfoldable,
          trivial
        end
  }

-- PROJECT finish this
-- lemma {u1 v1 u2 v2} FullyFaithfulEssentiallySurjective_Functors_are_Equivalences
--   { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
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
--       isomorphism_1 := begin
--                          pointwise,
--                          {
--                            -- Construct the forward map
--                            pointwise,
--                            all_goals { intros },
--                            unfold_unfoldable,
--                            exact (full _ _).val (essentially_surjective (F.onObjects X)).2.morphism,
--                            unfold_unfoldable,
                           
--                          }
--                        end,
--       isomorphism_2 := sorry
--     },
--     ♮
--   ⟩

end tqft.categories.equivalence