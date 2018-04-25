-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import categories.isomorphism
import categories.functor_categories

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
   : (α.morphism.components X) ≫ (α.inverse.components X) = 𝟙 (F +> X)
   := congr_arg (λ β, NaturalTransformation.components β X) α.witness_1
@[simp,ematch] lemma NaturalIsomorphism.componentwise_witness_1_assoc
  (α : F ⇔ G)
  (X : C) (Z : D) (f : (F +> X) ⟶ Z)
   : (α.morphism.components X) ≫ (α.inverse.components X) ≫ f = f
   := by obviously
@[simp,ematch] lemma NaturalIsomorphism.componentwise_witness_2
  (α : F ⇔ G)
  (X : C)
   : (α.inverse.components X) ≫ (α.morphism.components X) = 𝟙 (G +> X)
   := congr_arg (λ β, NaturalTransformation.components β X) α.witness_2
@[simp,ematch] lemma NaturalIsomorphism.componentwise_witness_2_assoc
  (α : F ⇔ G)
  (X : C) (Z : D) (f : (G +> X) ⟶ Z)
   : (α.inverse.components X) ≫ (α.morphism.components X) ≫ f = f
   := by obviously

@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.naturality_1 
  (α : F ⇔ G)
  {X Y : C}
  (f : X ⟶ Y)
   : (α.inverse.components X) ≫ (F &> f) ≫ (α.morphism.components Y) = G &> f := by obviously

@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.naturality_2 
  (α : F ⇔ G)
  {X Y : C}
  (f : X ⟶ Y)
   : (α.morphism.components X) ≫ (G &> f) ≫ (α.inverse.components Y) = F &> f := by obviously

definition NaturalIsomorphism.from_components
  (components : ∀ X : C, (F +> X) ≅ (G +> X))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), (F &> f) ≫ (components Y).morphism = (components X).morphism ≫ (G &> f)) : NaturalIsomorphism F G :=
{ morphism  := { components := λ X, (components X).morphism, },
  inverse   := { components := λ X, (components X).inverse,
                 naturality := λ X Y f, begin 
                                          let p := congr_arg (λ f, (components X).inverse ≫ (f ≫ (components Y).inverse)) (eq.symm (naturality f)),
                                          tidy,
                                        end } }

definition vertical_composition_of_NaturalIsomorphisms (α : F ⇔ G) (β : G ⇔ H) : F ⇔ H :=
Isomorphism.comp α β

attribute [reducible] NaturalIsomorphism

open NaturalTransformation

definition is_NaturalIsomorphism  (α : F ⟹ G) := @is_Isomorphism (C ↝ D) _ F G α
attribute [class] is_NaturalIsomorphism

@[ematch] lemma is_NaturalIsomorphism_componentwise_witness_1
  (α : F ⟹ G)
  (w : is_NaturalIsomorphism α)
  (X : C)
   : (α.components X) ≫ (w.inverse.components X) = 𝟙 (F +> X)
   := congr_arg (λ β, NaturalTransformation.components β X) w.witness_1
@[ematch] lemma is_NaturalIsomorphism_componentwise_witness_2
  (α : F ⟹ G)
  (w : is_NaturalIsomorphism α)
  (X : C)
   : (w.inverse.components X) ≫ (α.components X) = 𝟙 (G +> X)
   := congr_arg (λ β, NaturalTransformation.components β X) w.witness_2

instance (F : C ↝ D) : is_NaturalIsomorphism (1 : F ⟹ F) := {
    inverse := 1
}

instance NaturalIsomorphism.morphism.is_NaturalIsomorphism {F G : C ↝ D} (α : F ⇔ G) : is_NaturalIsomorphism (α.morphism) := 
{ inverse := α.inverse }
instance NaturalIsomorphism.inverse.is_NaturalIsomorphism  {F G : C ↝ D} (α : F ⇔ G) : is_NaturalIsomorphism (α.inverse) := 
{ inverse := α.morphism }

@[reducible] definition NaturalIsomorphism.components {F G : C ↝ D} (α : F ⇔ G) (X : C) : (F +> X) ≅ (G +> X) := 
{ morphism := α.morphism.components X,
  inverse  := α.inverse.components X }

instance NaturalIsomorphism.morphisms.components.is_Isomorphism {F G : C ↝ D} (α : F ⇔ G) (X : C) : is_Isomorphism (α.morphism.components X) := 
{ inverse := α.inverse.components X }
instance NaturalIsomorphism.inverse.components.is_Isomorphism   {F G : C ↝ D} (α : F ⇔ G) (X : C) : is_Isomorphism (α.inverse.components X) := 
{ inverse := α.morphism.components X }

@[reducible] definition NaturalIsomorphism.reverse {F G : C ↝ D} (α : F ⇔ G) : G ⇔ F := {
    morphism := α.inverse,
    inverse := α.morphism
}

end categories.natural_transformation
