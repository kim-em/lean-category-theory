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

universes u₁ u₂ u₃

structure Equivalence (C : Type u₁) [category C] (D : Type u₂) [category D] :=
  (functor : Functor C D)
  (inverse : Functor D C)
  (isomorphism_1 : NaturalIsomorphism (FunctorComposition functor inverse) (IdentityFunctor C) . obviously)
  (isomorphism_2 : NaturalIsomorphism (FunctorComposition inverse functor) (IdentityFunctor D) . obviously)

variable {C : Type u₁}
variable [category C]
variable {D : Type u₂}
variable [category D]
variable {E : Type u₃}
variable [category E]

definition is_Equivalence (F : Functor C D) := {e : Equivalence C D // e.functor = F} -- TODO yuck!

definition Equivalence.reverse (e : Equivalence C D) : Equivalence D C :=
{
  functor := e.inverse,
  inverse := e.functor,
  isomorphism_1 := e.isomorphism_2,
  isomorphism_2 := e.isomorphism_1
}

definition EquivalenceComposition
  (e : Equivalence C D)
  (f : Equivalence D E)
   : Equivalence C E := {
  functor := FunctorComposition e.functor f.functor,
  inverse := FunctorComposition f.inverse e.inverse,
  isomorphism_1 := 
    (
      calc
             FunctorComposition e.functor (FunctorComposition (FunctorComposition f.functor f.inverse) e.inverse)
          ≅ₙ FunctorComposition e.functor e.inverse
           : NaturalIsomorphism'.mkNatIso
               (Functor.onIsomorphisms (whisker_on_right_functor C e.inverse)
                 (Functor.onIsomorphisms (whisker_on_left_functor D e.functor) f.isomorphism_1))
      ... ≅ₙ IdentityFunctor C
           : NaturalIsomorphism'.mkNatIso e.isomorphism_1
    ).iso,
  isomorphism_2 :=
    (
      calc
            FunctorComposition f.inverse (FunctorComposition (FunctorComposition e.inverse e.functor) f.functor)
          ≅ₙ FunctorComposition f.inverse f.functor
           : NaturalIsomorphism'.mkNatIso
               (Functor.onIsomorphisms (whisker_on_right_functor E f.functor)
                 (Functor.onIsomorphisms (whisker_on_left_functor D f.inverse) e.isomorphism_2))
      ... ≅ₙ IdentityFunctor E
           : NaturalIsomorphism'.mkNatIso f.isomorphism_2
    ).iso
}

structure Full (F : Functor C D) :=
  (preimage : ∀ {X Y : C} (f : Hom (F.onObjects X) (F.onObjects Y)), C.Hom X Y)
  (witness  : ∀ {X Y : C} (f : Hom (F.onObjects X) (F.onObjects Y)), F.onMorphisms (preimage f) = f)

attribute [semiapplicable] Full.preimage 

attribute [simp,ematch] Full.witness

structure Faithful (F : Functor C D) :=
  (injectivity : ∀ {X Y : C.Obj} (f g : C.Hom X Y) (p : F.onMorphisms f = F.onMorphisms g), f = g)

attribute [semiapplicable] Faithful.injectivity

definition Embedding (F : Functor C D) := (Full F) × (Faithful F)

definition EssentiallySurjective (F : Functor C D) := Π d : D.Obj, Σ c : C.Obj, Isomorphism D (F.onObjects c) d

end categories.equivalence