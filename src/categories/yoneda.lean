-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .isomorphism
import .opposites
import .equivalence
import .products.switch
import .types

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

definition Yoneda (C : Type u₁) [category C] : Functor C (Functor (Cᵒᵖ) (Type u₁)) :=
{
    onObjects := λ X, {
        onObjects     := λ Y, @Hom C _ Y X,
        onMorphisms   := λ Y Y' f, ulift.up (λ g, f >> g)
   },
    onMorphisms   := λ X X' f, {
        components := λ Y, ulift.up (λ g, g >> f)
   }
}

definition CoYoneda (C : Type u₁) [category C] : Functor (Cᵒᵖ) (Functor C (Type u₁)) :=
{
    onObjects := λ X, {
        onObjects     := λ Y, @Hom C _ X Y,
        onMorphisms   := λ Y Y' f, ulift.up (λ g, g >> f)
   },
    onMorphisms   := λ X X' f, {
        components := λ Y, ulift.up (λ g, f >> g)
   }
}

variable {C : Type u₁}
variable [category C]

class Representable (F : Functor C (Type u₁)) := 
  (c : C)
  (Φ : NaturalIsomorphism F ((CoYoneda C).onObjects c))

@[reducible] definition {v} YonedaEvaluation (C : Category.{v v})
  : Functor (ProductCategory (FunctorCategory (Opposite C) CategoryOfTypes.{v}) (Opposite C)) CategoryOfTypes.{v}
  := Evaluation (Opposite C) CategoryOfTypes.{v}
@[reducible] definition {v} YonedaPairing (C : Category.{v v}) 
  : Functor (ProductCategory (FunctorCategory (Opposite C) CategoryOfTypes.{v}) (Opposite C)) CategoryOfTypes.{v}
  := FunctorComposition
      (FunctorComposition
        (ProductFunctor (IdentityFunctor _) (OppositeFunctor (Yoneda C)))
        (SwitchProductCategory _ _))
      (HomPairing (FunctorCategory (Opposite C) CategoryOfTypes.{v})) 

@[simp] private lemma YonedaLemma_aux_1
   {C : Category}
   {X Y : C.Obj}
   (f : C.Hom X Y)
   {F G : Functor (Opposite C) CategoryOfTypes}
   (τ : NaturalTransformation F G)
   (Z : F.onObjects Y) :
     G.onMorphisms f (τ.components Y Z) = τ.components X (F.onMorphisms f Z) := eq.symm (congr_fun (τ.naturality f) Z)

theorem {v} YonedaLemma (C : Category.{v v}) : NaturalIsomorphism (YonedaPairing C) (YonedaEvaluation C) := 
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

theorem {u v} YonedaEmbedding (C : Category.{u v}) : Embedding (Yoneda C) :=
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