-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .isomorphism
import .functor_categories

open categories
open categories.isomorphism
open categories.functor
open categories.functor_categories

namespace categories.natural_transformation

universes u₁ u₂ v₁ v₂

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

definition NaturalIsomorphism (F G : C ↝ D) := F ≅ G

infix ` ⇔ `:10 := NaturalIsomorphism -- type as \<=>

-- It's a pity we need to separately define this coercion.
-- Ideally the coercion from Isomorphism along .morphism would just apply here.
-- Somehow we want the definition above to be more transparent?
instance NaturalIsomorphism_coercion_to_NaturalTransformation (F G : C ↝ D) : has_coe (F ⇔ G) (F ⟹ G) :=
  {coe := Isomorphism.morphism}

variables {F G H : C ↝ D}

@[simp,ematch] lemma NaturalIsomorphism.componentwise_witness_1
  (α : F ⇔ G)
  (X : C)
   : (α.morphism.components X) ≫ (α.inverse.components X) = 𝟙 (F X)
   := congr_arg (λ β, NaturalTransformation.components β X) α.witness_1
@[simp,ematch] lemma NaturalIsomorphism.componentwise_witness_1_assoc
  (α : NaturalIsomorphism F G)
  (X : C) (Z : D) (f : Hom (F X) Z)
   : (α.morphism.components X) ≫ (α.inverse.components X) ≫ f = f
   := begin rw ← category.associativity, simp end
@[simp,ematch] lemma NaturalIsomorphism.componentwise_witness_2
  (α : NaturalIsomorphism F G)
  (X : C)
   : (α.inverse.components X) ≫ (α.morphism.components X) = 𝟙 (G X)
   := congr_arg (λ β, NaturalTransformation.components β X) α.witness_2
@[simp,ematch] lemma NaturalIsomorphism.componentwise_witness_2_assoc
  (α : NaturalIsomorphism F G)
  (X : C) (Z : D) (f : Hom (G X) Z)
   : (α.inverse.components X) ≫ (α.morphism.components X) ≫ f = f
   := begin rw ← category.associativity, simp end

@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.naturality_1 
  (α : NaturalIsomorphism F G)
  {X Y : C}
  (f : Hom X Y)
   : (α.inverse.components X) ≫ (F &> f) ≫ (α.morphism.components Y) = G &> f := ♯

@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.naturality_2 
  (α : NaturalIsomorphism F G)
  {X Y : C}
  (f : Hom X Y)
   : (α.morphism.components X) ≫ (G &> f) ≫ (α.inverse.components Y) = F &> f := ♯

definition NaturalIsomorphism.from_components
  (components : ∀ X : C, Isomorphism (F X) (G X))
  (naturality : ∀ {X Y : C} (f : Hom X Y), (F &> f) ≫ (components Y).morphism = (components X).morphism ≫ (G &> f)) : NaturalIsomorphism F G :=
  {
    morphism  := {
      components := λ X, (components X).morphism,
   },
    inverse   := {
      components := λ X, (components X).inverse,
      naturality := λ X Y f, begin
                               let p := congr_arg (λ f, (components X).inverse ≫ (f ≫ (components Y).inverse)) (eq.symm (naturality f)),
                               simp at p,
                               exact p,
                             end
   }
 }

definition vertical_composition_of_NaturalIsomorphisms 
  (α : NaturalIsomorphism F G)
  (β : NaturalIsomorphism G H)
   : NaturalIsomorphism F H :=
  IsomorphismComposition α β

attribute [reducible] NaturalIsomorphism

-- TODO is this actually used?
-- New type for isomorphisms in functor categories. This specialisation helps type inference.
-- structure NaturalIsomorphism' (F G : Functor C D) :=
--   mkNatIso :: (iso : Isomorphism F G)

-- infix `≅ₙ`:50 := NaturalIsomorphism'

-- @[trans] definition NaturalIsomorphismComposition
--   (α : F ≅ₙ G) (β : G ≅ₙ H) : F ≅ₙ H :=
--   NaturalIsomorphism'.mkNatIso (vertical_composition_of_NaturalIsomorphisms α.iso β.iso)

open NaturalTransformation

definition is_NaturalIsomorphism  (α : F ⟹ G) := @is_Isomorphism (C ↝ D) _ F G α

@[ematch] lemma is_NaturalIsomorphism_componentwise_witness_1
  (α : NaturalTransformation F G)
  (w : is_NaturalIsomorphism α)
  (X : C)
   : (α.components X) ≫ (w.inverse.components X) = 𝟙 (F X)
   := congr_arg (λ β, NaturalTransformation.components β X) w.witness_1
@[ematch] lemma is_NaturalIsomorphism_componentwise_witness_2
  (α : NaturalTransformation F G)
  (w : is_NaturalIsomorphism α)
  (X : C)
   : (w.inverse.components X) ≫ (α.components X) = 𝟙 (G X)
   := congr_arg (λ β, NaturalTransformation.components β X) w.witness_2


lemma IdentityNaturalTransformation_is_NaturalIsomorphism (F : C ↝ D) : is_NaturalIsomorphism (1 : F ⟹ F) := {
    inverse := 1
}

definition NaturalIsomorphism.components {F G : C ↝ D} (α : F ⇔ G) (X : C) : (F X) ≅ (G X) := {
    morphism := α.morphism.components X,
    inverse := α.inverse.components X
}

definition NaturalIsomorphism.reverse {F G : C ↝ D} (α : F ⇔ G) : G ⇔ F := {
    morphism := α.inverse,
    inverse := α.morphism
}

end categories.natural_transformation
