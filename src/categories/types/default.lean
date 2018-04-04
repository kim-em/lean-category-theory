-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..isomorphism
import ..functor
import ..natural_transformation

namespace categories.types

open categories
open categories.isomorphism
open categories.functor

universes u v w

instance CategoryOfTypes : category (Type u) :=
{
    Hom := λ a b, (a → b),
    identity := λ a, id,
    compose  := λ _ _ _ f g, g ∘ f
}

variables {C : Type (v+1)} [category C] (F G H: Functor C (Type u)) {X Y Z : C} 
variables (σ : F ⟹ G) (τ : G ⟹ H) 

@[simp] lemma Functor_to_Types.functoriality (f : X ⟶ Y) (g : Y ⟶ Z) (a : F X) : (F &> (f ≫ g)) a = (F &> g) ((F &> f) a) := by obviously
@[simp] lemma Functor_to_Types.identities (a : F X) : (F &> (𝟙 X)) a = a := by obviously
@[ematch] lemma Functor_to_Types.naturality (f : X ⟶ Y) (x : F X) : σ.components Y ((F &> f) x) = (G &> f) (σ.components X x) := 
begin 
  have p := σ.naturality_lemma f,
  tidy,
end.
@[simp] lemma Functor_to_Types.vertical_composition (x : F X) : (σ ⊟ τ).components X x = τ.components X (σ.components X x) := by obviously 

-- TODO
-- variables {D : Type (w+1)} [category D] (I J : D ↝ C) (ρ : I ⟹ J) {W : D}
-- @[simp] lemma Functor_to_Types.horizontal_composition (x : (I ⋙ F) W) : (ρ ◫ σ).components W x = sorry := by obviously 


definition UniverseLift : Functor (Type u) (Type (u+1)) := {
    onObjects := λ X, ulift.{u+1} X,
    onMorphisms := λ X Y f, λ x : ulift.{u+1} X, ulift.up (f x.down)
}

definition Bijection (α β : Type u) := Isomorphism α β 

@[simp] definition Bijection.witness_1 {α β : Type u} (iso : Bijection α β) (x : α) : iso.inverse (iso.morphism x) = x :=
begin
  have p := iso.witness_1_lemma, unfold_projs at p,
  tidy,
end
@[simp] definition Bijection.witness_2 {α β : Type u} (iso : Bijection α β) (x : β) : iso.morphism (iso.inverse x) = x :=
begin
  have p := iso.witness_2_lemma, unfold_projs at p,
  tidy,
end

-- TODO the @s are unpleasant here
@[simp] definition is_Isomorphism_in_Types.witness_1 {α β : Type u} (f : α → β) (h : @is_Isomorphism _ _ α β f) (x : α) : h.inverse (f x) = x :=
begin
  have p := h.witness_1, unfold_projs at p,
  tidy,
end
@[simp] definition is_Isomorphism_in_Types.witness_2 {α β : Type u} (f : α → β) (h : @is_Isomorphism _ _ α β f) (x : β) : f (h.inverse x) = x :=
begin
  have p := h.witness_2, unfold_projs at p,
  tidy,
end


end categories.types
