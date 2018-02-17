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
import .universe_lifting

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

definition YonedaEvaluation (C : Type u₁) [category C]
  : Functor.{(u₁+1) (u₁+2)} ((Functor (Cᵒᵖ) (Type u₁)) × (Cᵒᵖ)) (Type (u₁+1))
  := FunctorComposition (Evaluation (Cᵒᵖ) (Type u₁)) (UniverseLift)

definition Yoneda (C : Type u₁) [category C] : Functor.{u₁ (u₁+1)} C (Functor (Cᵒᵖ) (Type u₁)) := {
    onObjects := λ X, {
        onObjects     := λ Y, @Hom C _ Y X,
        onMorphisms   := λ Y Y' f, ulift.up (λ g, f ≫ g)
   },
    onMorphisms   := λ X X' f, {
        components := λ Y, ulift.up (λ g, g ≫ f)
   }
}

definition YonedaPairing (C : Type u₁) [category C] 
  : Functor.{(u₁+1) (u₁+2)} ((Functor (Cᵒᵖ) (Type u₁)) × (Cᵒᵖ)) (Type (u₁+1)) 
  := FunctorComposition
      (FunctorComposition
        (ProductFunctor (IdentityFunctor _) (OppositeFunctor (Yoneda C)))
        (SwitchProductCategory _ _))
      (HomPairing (Functor (Cᵒᵖ) (Type u₁))) 

definition CoYoneda (C : Type u₁) [category C] : Functor.{u₁ (u₁+1)} (Cᵒᵖ) (Functor C (Type u₁)) := {
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

@[simp] private lemma YonedaLemma_aux_1
   {X Y : C}
   (f : Hom X Y)
   {F G : Functor (Cᵒᵖ) (Type u₁)}
   (τ : NaturalTransformation F G)
   (Z : F.onObjects Y) :
     (G.onMorphisms f).down ((τ.components Y).down Z) = (τ.components X).down ((F.onMorphisms f).down Z) := eq.symm (congr_fun (congr_arg ulift.down (τ.naturality f)) Z)

-- @[simp] private lemma YonedaLemma_aux_2
--   {D : Type u₂}
--   [category D]
--   {X : (Cᵒᵖ)}
--   {F : Functor (Cᵒᵖ) D} : (F.onMorphisms (@categories.category.identity.{u₁} C _ X)) = 𝟙 (F.onObjects X) :=
--   begin
--   have h : (@categories.category.identity.{u₁} C _ X) = (@categories.category.identity.{u₁} (categories.opposites.op.{u₁} C)
--              (@categories.opposites.Opposite.{u₁} C _)
--              X), by tidy,
--   rw h,
--   simp,
--   end


-- set_option pp.all true
-- @[simp] private lemma YonedaLemma_aux_2
--   {X_snd : (Cᵒᵖ)}
--   {X_fst : Functor (Cᵒᵖ) (Type u₁)}
--   (x : X_fst.onObjects X_snd) : (X_fst.onMorphisms (@categories.category.identity.{u₁} C _ X_snd)).down x  = x :=
--   begin
--   have h : (@categories.category.identity.{u₁} C _ X_snd) = (@categories.category.identity.{u₁} (categories.opposites.op.{u₁} C)
--              (@categories.opposites.Opposite.{u₁} C _inst_1)
--              X_snd), by tidy,
--   rw h,
--   simp,
--   end

theorem YonedaLemma (C : Type u₁) [category C]: NaturalIsomorphism (YonedaPairing C) (YonedaEvaluation C) := 
begin
refine {
  morphism := {
    components := λ F, ulift.up (λ x, ulift.up ((x.components F.2).down (𝟙 F.2))),
    naturality := _,
  },
  inverse := {
    components := λ F, ulift.up (λ x, { 
      components := λ X, ulift.up (λ a, (F.1.onMorphisms a).down x.down), 
      naturality := _ }),
    naturality := _
  },
  witness_1 := _,
  witness_2 := _
},
tidy {hints:=[9, 7, 6, 6, 7, 6, 9, 10, 9, 7, 6, 6, 7, 9, 10, 9, 7, 6, 6, 7, 6, 7, 6, 6, 7, 9, 10, 6, 7, 6, 6, 7, 6, 7, 6, 6, 7, 9, 10, 6, 7, 6, 6, 7, 6, 9, 10]}
end

-- theorem YonedaEmbedding (C : Type u₁) [category C] : Embedding (Yoneda C) :=
-- begin
--   unfold Embedding,
--   fsplit,
--   {
--     -- Show it is full
--     fsplit,
--     {
--         tidy,
--         exact (f.components X).down (𝟙 X)
--    },
--     {
--         tidy,
--         have q := congr_fun (congr_arg ulift.down (f.naturality x)) (𝟙 X),
--         tidy,
--    }
--  },
--   {
--     -- Show it is faithful
--     tidy,
--     have q := congr_fun p X,
--     have q' := congr_fun q (𝟙 X),
--     tidy,
--  }
-- end

end categories.yoneda