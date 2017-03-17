-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category

namespace tqft.categories.monoidal_functor

structure MonoidalFunctor ( C D : MonoidalCategory ) :=
  ( functor : Functor C D )
  ( tensorator : NaturalIsomorphism (FunctorComposition C^.tensor functor) (FunctorComposition (functor × functor) D^.tensor) )
  -- TODO identerator and axiom
  -- TODO associativity of the tensorator!

instance MonoidalFunctor_coercion_to_functor { C D : MonoidalCategory } : has_coe (MonoidalFunctor C D) (Functor C D) :=
  { coe := MonoidalFunctor.functor }

structure MonoidalNaturalTransformation { C D : MonoidalCategory } ( F G : MonoidalFunctor C D ) :=
  ( natural_transformation : NaturalTransformation F^.functor G^.functor )
  ( compatibility_with_tensor : ∀ X Y : C^.Obj, D^.compose (natural_transformation (C^.tensorObjects X Y)) (G^.tensorator (X, Y)) = D^.compose (F^.tensorator (X, Y)) (D^.tensorMorphisms (natural_transformation X) (natural_transformation Y)) )
-- TODO compatibility with unit

attribute [ematch,simp] MonoidalNaturalTransformation.compatibility_with_tensor

-- TODO this is obtuse
@[pointwise] lemma MonoidalNaturalTransformation_componentwise_equal
  { C D : MonoidalCategory }
  { F G : MonoidalFunctor C D }
  ( α β : MonoidalNaturalTransformation F G )
  ( w : α^.natural_transformation = β^.natural_transformation ) : α = β :=
  begin
    induction α with α_components α_naturality,
    induction β with β_components β_naturality,
    blast
  end

instance MonoidalNaturalTransformation_coercion_to_natural_transformation
  { C D : MonoidalCategory }
  ( F G : MonoidalFunctor C D ) : has_coe (MonoidalNaturalTransformation F G) (NaturalTransformation F^.functor G^.functor) :=
  { coe := MonoidalNaturalTransformation.natural_transformation }

local attribute [reducible] lift_t coe_t coe_b

@[reducible] definition vertical_composition_of_MonoidalNaturalTransformations
  { C D : MonoidalCategory } 
  { F G H : MonoidalFunctor C D } 
  ( α : MonoidalNaturalTransformation F G ) 
  ( β : MonoidalNaturalTransformation G H ) : MonoidalNaturalTransformation F H :=
{
  natural_transformation    := vertical_composition_of_NaturalTransformations α^.natural_transformation β^.natural_transformation,
  compatibility_with_tensor := begin
                                abstract {
                                  -- TODO It seems that one round of blast should succeed here!
                                  blast,
                                  rewrite D^.associativity,
                                  simp,
                                  rewrite - D^.associativity,
                                  simp,
                                  blast
                                }
                               end
}

-- TODO horizontal_composition_of_MonoidalNaturalTransformations

definition CategoryOfMonoidalFunctors ( C D : MonoidalCategory ) : Category :=
{
  Obj := MonoidalFunctor C D,
  Hom := λ F G, MonoidalNaturalTransformation F G,
  identity := λ F, ⟨ IdentityNaturalTransformation F, ♮ ⟩,
  compose  := λ _ _ _ α β, vertical_composition_of_MonoidalNaturalTransformations α β,

  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

end tqft.categories.monoidal_functor