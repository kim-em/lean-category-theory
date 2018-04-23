-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.natural_transformation
import categories.isomorphism
import categories.opposites
import categories.equivalence
import categories.products.switch
import categories.types
import categories.functor_categories.evaluation
import categories.universe_lifting

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

definition YonedaEvaluation (C : Type (u₁+1)) [category C]
  : (((Cᵒᵖ) ↝ (Type u₁)) × (Cᵒᵖ)) ↝ (Type (u₁+1)) 
  := (Evaluation (Cᵒᵖ) (Type u₁)) ⋙ UniverseLift

definition Yoneda (C : Type (u₁+1)) [category C] : Functor C (Functor (Cᵒᵖ) (Type u₁)) := {
    onObjects := λ X, {
        onObjects     := λ Y, @category.Hom C _ Y X,
        onMorphisms   := λ Y Y' f g, f ≫ g
   },
    onMorphisms   := λ X X' f, {
        components := λ Y g, g ≫ f
   }
}

definition YonedaPairing (C : Type (u₁+1)) [category C] 
  : (((Cᵒᵖ) ↝ (Type u₁)) × (Cᵒᵖ)) ↝ (Type (u₁+1)) 
  := (ProductFunctor (IdentityFunctor _) (OppositeFunctor (Yoneda C))) ⋙ 
      (SwitchProductCategory _ _) ⋙ 
       (HomPairing ((Cᵒᵖ) ↝ (Type u₁))) 

definition CoYoneda (C : Type (u₁+1)) [category C] : (Cᵒᵖ) ↝ (C ↝ (Type u₁)) := {
    onObjects := λ X, {
        onObjects     := λ Y, @category.Hom C _ X Y,
        onMorphisms   := λ Y Y' f g, g ≫ f
   },
    onMorphisms   := λ X X' f, {
        components := λ Y g, f ≫ g
   }
}


variable {C : Type (u₁+1)}
variable [category C]

class Representable (F : C ↝ (Type u₁)) := 
  (c : C)
  (Φ : F ⇔ ((CoYoneda C) +> c))

@[simp] private lemma YonedaLemma_aux_1
   {X Y : C}
   (f : X ⟶ Y)
   {F G : (Cᵒᵖ) ↝ (Type u₁)}
   (τ : F ⟹ G)
   (Z : F +> Y) :
     (G &> f) ((τ.components Y) Z) = (τ.components X) ((F &> f) Z) := eq.symm (congr_fun (τ.naturality f) Z)

local attribute [tidy] dsimp_all'

theorem YonedaLemma (C : Type (u₁+1)) [category C] : (YonedaPairing C) ⇔ (YonedaEvaluation C) := 
{ morphism := { components := λ F x, ulift.up ((x.components F.2) (𝟙 F.2)) },
  inverse  := { components := λ F x, { components := λ X a, (F.1 &> a) x.down } } }.

theorem YonedaFull (C : Type (u₁+1)) [category C] : Full (Yoneda C) := 
{ preimage := λ X Y f, (f.components X) (𝟙 X),
  witness := λ X Y f, begin tidy, have p := congr_fun (f.naturality x) (𝟙 X), tidy, end } -- PROJECT a pure rewriting proof?

theorem YonedaFaithful (C : Type (u₁+1)) [category C] : Faithful (Yoneda C) := {
    injectivity := λ X Y f g w, begin 
                                  -- PROJECT automation
                                  dsimp_all',
                                  have p := congr_arg NaturalTransformation.components w, 
                                  have p' := congr_fun p X, 
                                  have p'' := congr_fun p' (𝟙 X),
                                  tidy,
                                end
}

end categories.yoneda