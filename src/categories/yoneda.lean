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

universes u₁ v₁ u₂

section
variables (C : Type u₁) [category.{u₁ v₁} C]

-- FIXME why isn't this already available?
instance : category ((Cᵒᵖ) ↝ Type v₁ × (Cᵒᵖ)) := products.ProductCategory.{(max u₁ (v₁+1)) (max u₁ v₁) u₁ v₁} (Cᵒᵖ ↝ Type v₁) (Cᵒᵖ)

definition YonedaEvaluation 
  : (((Cᵒᵖ) ↝ (Type v₁)) × (Cᵒᵖ)) ↝ (Type (max u₁ v₁)) 
  := (Evaluation (Cᵒᵖ) (Type v₁)) ⋙ UniverseLift.{v₁ u₁}

definition Yoneda : C ↝ ((Cᵒᵖ) ↝ (Type v₁)) := 
{ onObjects := λ X, 
    { onObjects     := λ Y, @category.Hom C _ Y X,
      onMorphisms   := λ Y Y' f g, f ≫ g },
  onMorphisms   := λ X X' f, 
    { components := λ Y g, g ≫ f } }

-- FIXME typeclass resolution needs some help.
definition YonedaPairing : (((Cᵒᵖ) ↝ (Type v₁)) × (Cᵒᵖ)) ↝ (Type (max u₁ v₁)) := 
let F := (SwitchProductCategory ((Cᵒᵖ) ↝ (Type v₁)) (Cᵒᵖ)) in
let G := (ProductFunctor (OppositeFunctor (Yoneda C)) (IdentityFunctor ((Cᵒᵖ) ↝ (Type v₁)))) in
let H := (HomPairing ((Cᵒᵖ) ↝ (Type v₁))) in
begin
  letI : category (Cᵒᵖ × (Cᵒᵖ ↝ Type v₁)) := by apply_instance,
  exact (F ⋙ G ⋙ H)      
end

definition CoYoneda (C : Type u₁) [category.{u₁ v₁} C] : (Cᵒᵖ) ↝ (C ↝ (Type v₁)) := 
{ onObjects := λ X, 
   { onObjects     := λ Y, @category.Hom C _ X Y,
     onMorphisms   := λ Y Y' f g, g ≫ f },
  onMorphisms   := λ X X' f,
    { components := λ Y g, f ≫ g } }
end

section
variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞

class Representable (F : C ↝ (Type v₁)) := 
  (c : C)
  (Φ : F ⇔ ((CoYoneda C) +> c))
end


@[simp] private lemma YonedaLemma_aux_1 {C : Type u₁} [category.{u₁ v₁} C] {X Y : C} (f : X ⟶ Y) {F G : (Cᵒᵖ) ↝ (Type v₁)} (τ : F ⟹ G) (Z : F +> Y) :
     (G &> f) ((τ.components Y) Z) = (τ.components X) ((F &> f) Z) := eq.symm (congr_fun (τ.naturality f) Z)

local attribute [tidy] dsimp_all'

set_option pp.universes true

theorem YonedaLemma (C : Type u₁) [category.{u₁ v₁} C] : (YonedaPairing C) ⇔ (YonedaEvaluation C) := 
{ morphism := { components := λ F x, ulift.up ((x.components F.2) (𝟙 F.2)) },
  inverse  := { components := λ F x, { components := λ X a, (F.1 &> a) x.down } } }.

theorem YonedaFull (C : Type u₁) [category.{u₁ v₁} C] : Full (Yoneda C) := 
{ preimage := λ X Y f, (f.components X) (𝟙 X),
  witness := λ X Y f, begin tidy, have p := congr_fun (f.naturality x) (𝟙 X), tidy, end } -- PROJECT a pure rewriting proof?

theorem YonedaFaithful (C : Type u₁) [category.{u₁ v₁} C]  : Faithful (Yoneda C) := {
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