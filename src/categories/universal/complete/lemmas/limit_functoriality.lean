-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.instances

open category_theory
open category_theory.initial
open category_theory.universal

namespace category_theory.universal.lemmas.limit_functoriality

universe u
variable {J : Type u}
variable [small_category J]
variable {C : Type (u+1)}
variable [large_category C]
variable {F : J ↝ C}
variable {L : LimitCone F}
variable {X : Cone F}
variable {M : ColimitCocone F}
variable {Y : Cocone F}

@[back] private lemma uniqueness_of_morphism_to_limit
  {g : X.cone_point ⟶ L.obj.cone_point}
  (w : ∀ j : J, g ≫ ((L.obj).cone_maps j) = X.cone_maps j)
    : (L.«from»  X).cone_morphism = g :=
  begin
    let G : X ⟶ L.obj := ⟨ g, w ⟩,
    have q := L.uniqueness _ (L.«from» X) G,
    exact congr_arg ConeMorphism.cone_morphism q,
  end

@[simp,ematch] private lemma morphism_to_terminal_object_composed_with_cone_map
  {j : J}
    : (L.«from» X).cone_morphism ≫ (L.obj.cone_maps j) = X.cone_maps j :=
  (L.«from» X).commutativity j

@[back,reducible] def morphism_to_terminal_object_cone_point 
  {Z : C}
  (cone_maps : Π j : J, Z ⟶ (F j)) 
  (commutativity : Π j k : J, Π f : j ⟶ k, (cone_maps j) ≫ (F.map f) = cone_maps k)
   : Z ⟶ L.obj.cone_point :=
begin
  let cone : Cone F := {
    cone_point    := Z,
    cone_maps     := cone_maps,
    commutativity := commutativity
 },
  exact (L.«from» cone).cone_morphism, 
end

@[back] private lemma uniqueness_of_morphism_from_colimit
  {g : M.obj.cocone_point ⟶ Y.cocone_point}
  (w : ∀ j : J, ((M.obj).cocone_maps j) ≫ g = Y.cocone_maps j)
    : (M.to Y).cocone_morphism = g :=
  begin
    let G : M.obj ⟶ Y := ⟨ g, w ⟩,
    have q := M.uniqueness _ (M.to Y) G,
    exact congr_arg CoconeMorphism.cocone_morphism q,
  end

@[simp,ematch] private lemma cocone_map_composed_with_morphism_from_initial_object
  {j : J}
    : (M.obj.cocone_maps j) ≫ (M.to Y).cocone_morphism = Y.cocone_maps j :=
  (M.to Y).commutativity j

@[back,reducible] def morphism_from_initial_object_cocone_point 
  {Z : C}
  (cocone_maps : Π j : J, (F j) ⟶ Z) 
  (commutativity : Π j k : J, Π f : j ⟶ k, (F.map f) ≫ (cocone_maps k) = cocone_maps j)
   : M.obj.cocone_point ⟶ Z :=
begin
  let cocone : Cocone F := {
    cocone_point  := Z,
    cocone_maps   := cocone_maps,
    commutativity := commutativity
 },
  exact (M.to cocone).cocone_morphism, 
end

end category_theory.universal.lemmas.limit_functoriality
