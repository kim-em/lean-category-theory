-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.natural_transformation
import category_theory.opposites
import category_theory.types
import category_theory.products.switch
import category_theory.functor_categories.evaluation
import category_theory.universe_lifting
import category_theory.cancellation

import tactic.interactive

open category_theory

namespace category_theory.yoneda

universes u₁ v₁ u₂

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

def yoneda : C ↝ ((Cᵒᵖ) ↝ (Type v₁)) := 
{ obj := λ X, { obj := λ Y : C, Y ⟶ X,
                map' := λ Y Y' f g, f ≫ g },
  map' := λ X X' f, { app := λ Y g, g ≫ f } }

@[simp] lemma yoneda_obj_obj (X Y : C) : ((yoneda C) X) Y = (Y ⟶ X) := rfl
@[simp] lemma yoneda_obj_map (X : C) {Y Y' : C} (f : Y ⟶ Y') : ((yoneda C) X).map f = λ g, f ≫ g := rfl
@[simp] lemma yoneda_map_app {X X' : C} (f : X ⟶ X') (Y : C) : ((yoneda C).map f) Y = λ g, g ≫ f := rfl

@[ematch] lemma yoneda_aux_1 {X Y : Cᵒᵖ} (f : X ⟶ Y) : ((yoneda C).map f) Y (𝟙 Y) = ((yoneda C) X).map f (𝟙 X) := by obviously
@[simp,ematch] lemma yoneda_aux_2 {X Y : C} (α : (yoneda C) X ⟶ (yoneda C) Y) {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) : α Z (f ≫ h) = f ≫ α Z' h := by obviously

instance yoneda_full : full (yoneda C) := 
{ preimage := λ X Y f, (f X) (𝟙 X) }.

instance yoneda_faithful : faithful (yoneda C) := 
begin
/- obviously says: -/ 
fsplit, 
intros X Y f g p, 
injections_and_clear, 
have cancel_right'_f_g_h_1 := cancel_right' f g h_1, 
assumption
end

-- We need to help typeclass inference with some awkward universe levels here.
instance instance_1 : category (((Cᵒᵖ) ↝ Type v₁) × (Cᵒᵖ)) := category_theory.prod.{(max u₁ (v₁+1)) (max u₁ v₁) u₁ v₁} (Cᵒᵖ ↝ Type v₁) (Cᵒᵖ)
instance instance_2 : category ((Cᵒᵖ) × ((Cᵒᵖ) ↝ Type v₁)) := category_theory.prod.{u₁ v₁ (max u₁ (v₁+1)) (max u₁ v₁)} (Cᵒᵖ) (Cᵒᵖ ↝ Type v₁) 

def yoneda_evaluation : (((Cᵒᵖ) ↝ (Type v₁)) × (Cᵒᵖ)) ↝ (Type (max u₁ v₁)) 
  := (evaluation (Cᵒᵖ) (Type v₁)) ⋙ ulift_functor.{v₁ u₁}

@[simp] lemma yoneda_evaluation_map_down (P Q : (Cᵒᵖ ↝ Type v₁) ×  (Cᵒᵖ)) (α : P ⟶ Q) (x : (yoneda_evaluation C) P)
 : ((yoneda_evaluation C).map α x).down = (α.1) (Q.2) ((P.1).map (α.2) (x.down)) := rfl

def yoneda_pairing : (((Cᵒᵖ) ↝ (Type v₁)) × (Cᵒᵖ)) ↝ (Type (max u₁ v₁)) := 
let F := (prod.switch ((Cᵒᵖ) ↝ (Type v₁)) (Cᵒᵖ)) in
let G := (functor.prod ((yoneda C).op) (functor.id ((Cᵒᵖ) ↝ (Type v₁)))) in
let H := (functor.hom ((Cᵒᵖ) ↝ (Type v₁))) in
  (F ⋙ G ⋙ H)      

@[simp] lemma yoneda_pairing_map (P Q : (Cᵒᵖ ↝ Type v₁) ×  (Cᵒᵖ)) (α : P ⟶ Q) (β : (yoneda_pairing C) (P.1, P.2)): (yoneda_pairing C).map α β = (yoneda C).map (α.snd) ≫ β ≫ α.fst := rfl

def yoneda_lemma : (yoneda_pairing C) ⇔ (yoneda_evaluation C) := 
{ hom := { app := λ F x, ulift.up ((x.app F.2) (𝟙 F.2)) },
  inv := { app := λ F x, { app := λ X a, (F.1.map a) x.down } } }.

end category_theory.yoneda