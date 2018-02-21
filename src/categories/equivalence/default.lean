-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..natural_isomorphism

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.equivalence

universes u₁ u₂ u₃

structure Equivalence (C : Type (u₁+1)) [category C] (D : Type (u₂+1)) [category D] :=
  (functor : Functor C D)
  (inverse : Functor D C)
  (isomorphism_1 : NaturalIsomorphism (FunctorComposition functor inverse) (IdentityFunctor C))
  (isomorphism_2 : NaturalIsomorphism (FunctorComposition inverse functor) (IdentityFunctor D))

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]
variable {E : Type (u₃+1)}
variable [category E]

definition is_Equivalence (F : Functor C D) := {e : Equivalence C D // e.functor = F} -- TODO yuck!
structure is_Equivalence' (F : Functor C D) := 
  (inverse : Functor D C)
  (isomorphism_1 : NaturalIsomorphism (FunctorComposition F inverse) (IdentityFunctor C))
  (isomorphism_2 : NaturalIsomorphism (FunctorComposition inverse F) (IdentityFunctor D))


definition Equivalence.reverse (e : Equivalence C D) : Equivalence D C :=
{
  functor := e.inverse,
  inverse := e.functor,
  isomorphism_1 := e.isomorphism_2,
  isomorphism_2 := e.isomorphism_1
}

@[simp,ematch] lemma Equivalence.onMorphisms_1 (e : Equivalence C D) (X Y : D) (f : Hom X Y) : e.functor &> (e.inverse &> f) = (e.isomorphism_2.components X).morphism ≫ f ≫ (e.isomorphism_2.reverse.components Y).morphism := 
begin
tidy,
erw e.isomorphism_2.naturality_2,
tidy,
end
@[simp,ematch] lemma Equivalence.onMorphisms_2 (e : Equivalence C D) (X Y : C) (f : Hom X Y) : e.inverse &> (e.functor &> f) = (e.isomorphism_1.components X).morphism ≫ f ≫ (e.isomorphism_1.reverse.components Y).morphism := 
begin
tidy,
erw e.isomorphism_1.naturality_2,
tidy,
end

-- -- TODO this should have 3 relatives.
-- @[simp,ematch] lemma Equivalence.naturality_2 (e : Equivalence C D) {X Y : D} (f : Hom X Y)
--   :      e.functor &> (e.inverse &> f) ≫ ((e.isomorphism_2).morphism).components Y =
--          ((e.isomorphism_2).morphism).components X ≫ f :=
-- begin
-- erw ← ((e.isomorphism_2).morphism).naturality,
-- refl,
-- end



-- FIXME restore this
-- definition EquivalenceComposition
--   (e : Equivalence C D)
--   (f : Equivalence D E)
--    : Equivalence C E := {
--   functor := FunctorComposition e.functor f.functor,
--   inverse := FunctorComposition f.inverse e.inverse,
--   isomorphism_1 := 
--     (
--       calc
--              FunctorComposition e.functor (FunctorComposition (FunctorComposition f.functor f.inverse) e.inverse)
--           ≅ₙ FunctorComposition e.functor e.inverse
--            : NaturalIsomorphism'.mkNatIso
--                (Functor.onIsomorphisms (whisker_on_right_functor C e.inverse)
--                  (Functor.onIsomorphisms (whisker_on_left_functor e.functor D) f.isomorphism_1))
--       ... ≅ₙ IdentityFunctor C
--            : NaturalIsomorphism'.mkNatIso e.isomorphism_1
--     ).iso,
--   isomorphism_2 :=
--     (
--       calc
--             FunctorComposition f.inverse (FunctorComposition (FunctorComposition e.inverse e.functor) f.functor)
--           ≅ₙ FunctorComposition f.inverse f.functor
--            : NaturalIsomorphism'.mkNatIso
--                (Functor.onIsomorphisms (whisker_on_right_functor E f.functor)
--                  (Functor.onIsomorphisms (whisker_on_left_functor f.inverse D) e.isomorphism_2))
--       ... ≅ₙ IdentityFunctor E
--            : NaturalIsomorphism'.mkNatIso f.isomorphism_2
--     ).iso
-- }

structure Full (F : Functor C D) :=
  (preimage : ∀ {X Y : C} (f : Hom (F X) (F Y)), Hom X Y)
  (witness  : ∀ {X Y : C} (f : Hom (F X) (F Y)), F &> (preimage f) = f . obviously)

attribute [semiapplicable] Full.preimage
make_lemma Full.witness
attribute [simp,ematch] Full.witness_lemma

class Faithful (F : Functor C D) :=
  (injectivity : ∀ {X Y : C} (f g : Hom X Y) (p : F &> f = F &> g), f = g) -- FIXME writing '. obviously' here causes Lean to hang

make_lemma Faithful.injectivity
attribute [semiapplicable] Faithful.injectivity_lemma

definition Embedding (F : Functor C D) := (Full F) × (Faithful F)

definition EssentiallySurjective (F : Functor C D) := Π d : D, Σ c : C, Isomorphism (F c) d

end categories.equivalence