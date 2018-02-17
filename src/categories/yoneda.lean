-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .isomorphism
import .opposites
import .equivalence
import .products.switch
import .types
import .functor_categories.evaluation

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.isomorphism
open categories.equivalence
open categories.types
open categories.products
open categories.opposites

namespace categories.yoneda

universes u₁ u₂

definition Yoneda (C : Type u₁) [category C] : Functor.{u₁ (u₁+1)} C (Functor (Cᵒᵖ) (Type u₁)) :=
{
    onObjects := λ X, {
        onObjects     := λ Y, @Hom C _ Y X,
        onMorphisms   := λ Y Y' f, ulift.up (λ g, f ≫ g)
   },
    onMorphisms   := λ X X' f, {
        components := λ Y, ulift.up (λ g, g ≫ f)
   }
}

definition CoYoneda (C : Type u₁) [category C] : Functor.{u₁ (u₁+1)} (Cᵒᵖ) (Functor C (Type u₁)) :=
{
    onObjects := λ X, {
        onObjects     := λ Y, @Hom C _ X Y,
        onMorphisms   := λ Y Y' f, ulift.up (λ g, g ≫ f)
   },
    onMorphisms   := λ X X' f, {
        components := λ Y, ulift.up (λ g, f ≫ g)
   }
}

variable {C : Type u₁}
variable [category C]

class Representable (F : Functor C (Type u₁)) := 
  (c : C)
  (Φ : NaturalIsomorphism F ((CoYoneda C).onObjects c))

@[reducible] definition YonedaEvaluation (C : Type u₁) [category C]
  : Functor.{(u₁+1) (u₁+1)} ((Functor (Cᵒᵖ) (Type u₁)) × (Cᵒᵖ)) (Type u₁)
  := Evaluation (Cᵒᵖ) (Type u₁)
@[reducible] definition YonedaPairing (C : Type u₁) [category C] 
  : Functor.{(u₁+1) (u₁+1)} ((Functor (Cᵒᵖ) (Type u₁)) × (Cᵒᵖ)) (Type u₁) := {
    onObjects := λ F, NaturalTransformation F.1 ((Yoneda C).onObjects F.2)
  }
  -- := FunctorComposition
  --     (FunctorComposition
  --       (ProductFunctor (IdentityFunctor _) (OppositeFunctor (Yoneda C)))
  --       (SwitchProductCategory _ _))
  --     (HomPairing (Functor (Cᵒᵖ) (Type u₁))) 



@[simp] private lemma YonedaLemma_aux_1
   {X Y : C}
   (f : Hom X Y)
   {F G : Functor (Cᵒᵖ) (Type u₁)}
   (τ : NaturalTransformation F G)
   (Z : F.onObjects Y) :
     (G.onMorphisms f).down (τ.components Y Z) = τ.components X ((F.onMorphisms f).down Z) := eq.symm (congr_fun (τ.naturality f) Z)

theorem {v} YonedaLemma (C : Type u₁) [category C]: NaturalIsomorphism (YonedaPairing C) (YonedaEvaluation C) := 
begin
  fsplit,
  fsplit,
  intros,
  dsimp',
  intros,
  dsimp_all',
  automatic_induction,
  dsimp',
  dsimp_all',

  exact ((a.components _) (C.identity _)),

  dsimp',
  intros,
  fapply funext,
  intros,
  automatic_induction,
  dsimp',
  simp,
  fsplit,
  intros,
  dsimp',
  intros,
  fsplit,
  intros,
  dsimp',
  intros,
  dsimp_all',
  automatic_induction,
  dsimp',
  dsimp_all',

  exact ((X_fst.onMorphisms a_1) a),

  tidy {hints:=[9, 7, 6, 7, 11, 13, 9, 10, 3, 9, 7, 6, 7, 6, 7, 6, 7, 9, 11, 13, 9, 10, 3, 6, 7, 6, 7, 6, 7, 6, 7, 9, 11, 13, 9, 10, 6, 7, 6, 7, 9, 11, 13, 9, 10, 3]},
end

theorem YonedaEmbedding (C : Type u₁) [category C] : Embedding (Yoneda C) :=
begin
  unfold Embedding,
  fsplit,
  {
    -- Show it is full
    fsplit,
    {
        tidy,
        exact (f.components X) (C.identity X)
   },
    {
        tidy,
        have q := congr_fun (f.naturality x) (C.identity X),
        tidy,
   }
 },
  {
    -- Show it is faithful
    tidy,
    have q := congr_fun p X,
    have q' := congr_fun q (C.identity X),
    tidy,
 }
end

end categories.yoneda