-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.natural_transformation
import categories.opposites
import categories.products.switch
import categories.types
import categories.functor_categories.evaluation
import categories.universe_lifting
import categories.cancellation
import tactic.interactive

open category_theory

namespace category_theory.yoneda

universes u₁ v₁ u₂

section
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

-- We need to help typeclass inference with some awkward universe levels here.
instance instance_1 : category (((Cᵒᵖ) ↝ Type v₁) × (Cᵒᵖ)) := category_theory.prod.{(max u₁ (v₁+1)) (max u₁ v₁) u₁ v₁} (Cᵒᵖ ↝ Type v₁) (Cᵒᵖ)
instance instance_2 : category ((Cᵒᵖ) × ((Cᵒᵖ) ↝ Type v₁)) := category_theory.prod.{u₁ v₁ (max u₁ (v₁+1)) (max u₁ v₁)} (Cᵒᵖ) (Cᵒᵖ ↝ Type v₁) 

def yoneda_evaluation : (((Cᵒᵖ) ↝ (Type v₁)) × (Cᵒᵖ)) ↝ (Type (max u₁ v₁)) 
  := (evaluation (Cᵒᵖ) (Type v₁)) ⋙ type_lift.{v₁ u₁}

@[simp] lemma yoneda_evaluation_map_down (P Q : (Cᵒᵖ ↝ Type v₁) ×  (Cᵒᵖ)) (α : P ⟶ Q) (x : (yoneda_evaluation C) P)
 : ((yoneda_evaluation C).map α x).down = (α.1) (Q.2) ((P.1).map (α.2) (x.down)) := rfl

def yoneda : C ↝ ((Cᵒᵖ) ↝ (Type v₁)) := 
{ obj := λ X,      { obj := λ Y, @category.Hom C _ Y X,
                     map := λ Y Y' f g, f ≫ g },
  map := λ X X' f, { app := λ Y g, g ≫ f } }

@[simp] lemma yoneda_obj_obj (X Y : C) : ((yoneda C) X) Y = (Y ⟶ X) := rfl
@[simp] lemma yoneda_obj_map (X : C) {Y Y' : C} (f : Y ⟶ Y') : ((yoneda C) X).map f = λ g, f ≫ g := rfl
@[simp] lemma yoneda_map_app {X X' : C} (f : X ⟶ X') (Y : C) : ((yoneda C).map f) Y = λ g, g ≫ f := rfl

@[ematch] lemma yoneda_aux_1 {X Y : Cᵒᵖ} (f : X ⟶ Y) : ((yoneda C).map f) Y (𝟙 Y) = ((yoneda C) X).map f (𝟙 X) :=
begin
  dunfold yoneda,
  obviously,
end

section
local attribute [forward] congr_fun
local attribute [forward] nat_trans.naturality
@[simp,ematch] lemma yoneda_aux_2 {X Y : C} (α : (yoneda C) X ⟶ (yoneda C) Y) {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) : α Z (f ≫ h) = f ≫ α Z' h := 
begin
have p := nat_trans.naturality α,
  -- have p := α.naturality f,
  obviously,
end
end

@[simp,ematch] lemma yoneda_aux_3 {X Y : C} (α : (yoneda C) X ⟶ (yoneda C) Y) {Z : C} (f : Z ⟶ X) : f ≫ α X (𝟙 X) = α Z f := by obviously

def yoneda_pairing : (((Cᵒᵖ) ↝ (Type v₁)) × (Cᵒᵖ)) ↝ (Type (max u₁ v₁)) := 
let F := (prod.switch ((Cᵒᵖ) ↝ (Type v₁)) (Cᵒᵖ)) in
let G := (functor.prod ((yoneda C).opposite) (functor.id ((Cᵒᵖ) ↝ (Type v₁)))) in
let H := (hom_pairing ((Cᵒᵖ) ↝ (Type v₁))) in
  (F ⋙ G ⋙ H)      

@[simp] lemma yoneda_pairing_map (P Q : (Cᵒᵖ ↝ Type v₁) ×  (Cᵒᵖ)) (α : P ⟶ Q) (β : (yoneda_pairing C) (P.1, P.2)): (yoneda_pairing C).map α β = (yoneda C).map (α.snd) ≫ β ≫ α.fst := rfl

def coyoneda : (Cᵒᵖ) ↝ (C ↝ (Type v₁)) := 
{ obj := λ X,      { obj := λ Y, @category.Hom C _ X Y,
                     map := λ Y Y' f g, g ≫ f },
  map := λ X X' f, { app := λ Y g, f ≫ g } }

@[simp] lemma coyoneda_obj_obj (X Y : C) : ((coyoneda C) X) Y = (X ⟶ Y) := rfl
@[simp] lemma coyoneda_obj_map (X : C) {Y Y' : C} (f : Y ⟶ Y') : ((coyoneda C) X).map f = λ g, g ≫ f := rfl
@[simp] lemma coyoneda_map_app {X X' : C} (f : X ⟶ X') (Y : C) : ((coyoneda C).map f) Y = λ g, f ≫ g := rfl

end

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

class representable (F : C ↝ (Type v₁)) := 
(c : C)
(Φ : F ⇔ ((coyoneda C) c))

variable (C)

def yoneda_lemma : (yoneda_pairing C) ⇔ (yoneda_evaluation C) := 
{ hom := { app := λ F x, ulift.up ((x.app F.2) (𝟙 F.2)) },
  inv := { app := λ F x, { app := λ X a, (F.1.map a) x.down } } }.

instance yoneda_full : full (yoneda C) := 
{ preimage := λ X Y f, (f X) (𝟙 X) }

instance yoneda_faithful : faithful (yoneda C) := by obviously

def yoneda_embedding : embedding (yoneda C) := by obviously

end category_theory.yoneda