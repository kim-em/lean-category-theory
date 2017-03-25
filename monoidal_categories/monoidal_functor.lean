-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category
open tqft.categories.isomorphism

namespace tqft.categories.monoidal_functor

structure MonoidalFunctor ( C D : MonoidalCategory ) :=
  ( functor : Functor C D )
  ( tensorator : NaturalIsomorphism (FunctorComposition C^.tensor functor) (FunctorComposition (functor × functor) D^.tensor) )
  ( associativity : ∀ X Y Z : C^.Obj, 
      D^.compose (tensorator (C^.tensor (X, Y), Z)) (D^.compose (D^.tensorMorphisms (tensorator (X, Y)) (D^.identity (functor Z))) (D^.associator (functor X) (functor Y) (functor Z)))
      = D^.compose (functor^.onMorphisms (C^.associator X Y Z)) (D^.compose (tensorator (X, C^.tensor (Y, Z))) (D^.tensorMorphisms (D^.identity (functor X)) (tensorator (Y, Z))))
  )
  ( identerator : Isomorphism D (functor C^.tensor_unit) D^.tensor_unit)
  ( left_identity  : ∀ X : C^.Obj, D^.compose (tensorator (C^.tensor_unit, X)) (D^.compose (D^.tensorMorphisms identerator^.morphism (D^.identity (functor X))) (D^.left_unitor  (functor X))) = functor^.onMorphisms (C^.left_unitor X)  )
  ( right_identity : ∀ X : C^.Obj, D^.compose (tensorator (X, C^.tensor_unit)) (D^.compose (D^.tensorMorphisms (D^.identity (functor X)) identerator^.morphism) (D^.right_unitor (functor X))) = functor^.onMorphisms (C^.right_unitor X) )
  
attribute [ematch,simp] MonoidalFunctor.left_identity
attribute [ematch,simp] MonoidalFunctor.right_identity
attribute [ematch]      MonoidalFunctor.associativity

instance MonoidalFunctor_coercion_to_functor { C D : MonoidalCategory } : has_coe (MonoidalFunctor C D) (Functor C D) :=
  { coe := MonoidalFunctor.functor }

-- PROJECT composition of MonoidalFunctors

structure MonoidalNaturalTransformation { C D : MonoidalCategory } ( F G : MonoidalFunctor C D ) :=
  ( natural_transformation : NaturalTransformation F^.functor G^.functor )
  ( compatibility_with_tensor : ∀ X Y : C^.Obj, D^.compose (F^.tensorator (X, Y)) (D^.tensorMorphisms (natural_transformation X) (natural_transformation Y)) = D^.compose (natural_transformation (C^.tensorObjects X Y)) (G^.tensorator (X, Y)) )
  ( compatibility_with_unit   : D^.compose (natural_transformation C^.tensor_unit) G^.identerator^.morphism = F^.identerator^.morphism )

attribute [ematch,simp] MonoidalNaturalTransformation.compatibility_with_tensor
attribute [ematch,simp] MonoidalNaturalTransformation.compatibility_with_unit

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

instance MonoidalNaturalTransformation_coercion_to_NaturalTransformation
  { C D : MonoidalCategory }
  ( F G : MonoidalFunctor C D ) : has_coe (MonoidalNaturalTransformation F G) (NaturalTransformation F^.functor G^.functor) :=
  { coe := MonoidalNaturalTransformation.natural_transformation }

@[reducible] definition IdentityMonoidalNaturalTransformation
  { C D : MonoidalCategory }
  ( F : MonoidalFunctor C D ) : MonoidalNaturalTransformation F F :=
    ⟨ IdentityNaturalTransformation F^.functor, ♮, ♮ ⟩

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
                                  rewrite D^.interchange,
                                  rewrite - D^.associativity,
                                  rewrite α^.compatibility_with_tensor,
                                  rewrite D^.associativity,
                                  rewrite β^.compatibility_with_tensor,
                                  blast
                                }
                               end,
  compatibility_with_unit   := ♮                               
}

-- PROJECT horizontal_composition_of_MonoidalNaturalTransformations

definition CategoryOfMonoidalFunctors ( C D : MonoidalCategory ) : Category :=
{
  Obj := MonoidalFunctor C D,
  Hom := MonoidalNaturalTransformation,
  identity := IdentityMonoidalNaturalTransformation,
  compose  := λ _ _ _ α β, vertical_composition_of_MonoidalNaturalTransformations α β,

  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

end tqft.categories.monoidal_functor