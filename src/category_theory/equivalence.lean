-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .natural_isomorphism

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.equivalence

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

definition {u1 v1 u2 v2 u3 v3} EquivalenceComposition
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  ( e : Equivalence C D )
  ( f : Equivalence D E )
   : Equivalence C E := {
  functor := FunctorComposition e.functor f.functor,
  inverse := FunctorComposition f.inverse e.inverse,
  isomorphism_1 := 
    (
      calc
             FunctorComposition e.functor (FunctorComposition (FunctorComposition f.functor f.inverse) e.inverse)
          ≅ₙ FunctorComposition e.functor e.inverse
           : NaturalIsomorphism'.mkNatIso
               (Functor_onIsomorphisms (whisker_on_right_functor C e.inverse)
                 (Functor_onIsomorphisms (whisker_on_left_functor D e.functor) f.isomorphism_1))
      ... ≅ₙ IdentityFunctor C
           : NaturalIsomorphism'.mkNatIso e.isomorphism_1
     ).iso,
  isomorphism_2 :=
    (
      calc
            FunctorComposition f.inverse (FunctorComposition (FunctorComposition e.inverse e.functor) f.functor)
          ≅ₙ FunctorComposition f.inverse f.functor
           : NaturalIsomorphism'.mkNatIso
               (Functor_onIsomorphisms (whisker_on_right_functor E f.functor)
                 (Functor_onIsomorphisms (whisker_on_left_functor D f.inverse) e.isomorphism_2))
      ... ≅ₙ IdentityFunctor E
           : NaturalIsomorphism'.mkNatIso f.isomorphism_2
     ).iso
}

structure {u1 v1 u2 v2} Full     { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( preimage : ∀ { X Y : C.Obj } ( f : D.Hom (F.onObjects X) (F.onObjects Y) ), C.Hom X Y )
  ( witness  : ∀ { X Y : C.Obj } ( f : D.Hom (F.onObjects X) (F.onObjects Y) ), F.onMorphisms (preimage f) = f )

-- attribute [applicable] Full.preimage 
-- This would cause problems! 
-- It would be nice if we already had a full functor around, to be able to use it!
-- PROJECT we could achieve this if we could test whether apply would create new goals...
attribute [simp,ematch] Full.witness

structure {u1 v1 u2 v2} Faithful { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( injectivity : ∀ { X Y : C.Obj } ( f g : C.Hom X Y ) ( p : F.onMorphisms f = F.onMorphisms g ), f = g )

-- attribute [applicable] Faithful.injectivity
-- This would cause problems! We'd try to prove morphisms are equal by inventing faithful functors.
-- If they're already around, it's a good idea!


definition {u1 v1 u2 v2} Embedding { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := (Full F) × (Faithful F)

definition {u1 v1 u2 v2} EssentiallySurjective { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π d : D.Obj, Σ c : C.Obj, Isomorphism D (F.onObjects c) d

end categories.equivalence