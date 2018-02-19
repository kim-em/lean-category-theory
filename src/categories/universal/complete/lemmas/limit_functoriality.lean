-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ...instances

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.isomorphism
open categories.products
open categories.initial
open categories.types
open categories.universal

namespace categories.universal.lemmas.limit_functoriality

universe u
variable {J : Type (u+1)}
variable [category J]
variable {C : Type (u+2)}
variable [category C]
variable {F : Functor J C}
variable {L : LimitCone F}
variable {X : Cone F}
variable {M : ColimitCocone F}
variable {Y : Cocone F}

@[applicable] private lemma uniqueness_of_morphism_to_limit
  {g : Hom X.cone_point L.terminal_object.cone_point}
  (w : ∀ j : J, g ≫ ((L.terminal_object).cone_maps j) = X.cone_maps j)
    : (L.morphism_to_terminal_object_from X).cone_morphism = g :=
  begin
    let G : Hom X L.terminal_object := ⟨ g, w ⟩,
    have q := L.uniqueness_of_morphisms_to_terminal_object _ (L.morphism_to_terminal_object_from X) G,
    exact congr_arg ConeMorphism.cone_morphism q,
  end

@[simp,ematch] private lemma morphism_to_terminal_object_composed_with_cone_map
  {j : J}
    : (L.morphism_to_terminal_object_from X).cone_morphism ≫ (L.terminal_object.cone_maps j) = X.cone_maps j :=
  (L.morphism_to_terminal_object_from X).commutativity j

@[applicable,reducible] definition morphism_to_terminal_object_cone_point 
  {Z : C}
  (cone_maps : Π j : J, Hom Z (F.onObjects j)) 
  (commutativity : Π j k : J, Π f : Hom j k, (cone_maps j) ≫ (F.onMorphisms f) = cone_maps k)
   : Hom Z L.terminal_object.cone_point :=
begin
  let cone : Cone F := {
    cone_point    := Z,
    cone_maps     := cone_maps,
    commutativity := commutativity
 },
  exact (L.morphism_to_terminal_object_from cone).cone_morphism, 
end

@[applicable] private lemma uniqueness_of_morphism_from_colimit
  {g : Hom M.initial_object.cocone_point Y.cocone_point}
  (w : ∀ j : J, ((M.initial_object).cocone_maps j) ≫ g = Y.cocone_maps j)
    : (M.morphism_from_initial_object_to Y).cocone_morphism = g :=
  begin
    let G : Hom M.initial_object Y := ⟨ g, w ⟩,
    have q := M.uniqueness_of_morphisms_from_initial_object _ (M.morphism_from_initial_object_to Y) G,
    exact congr_arg CoconeMorphism.cocone_morphism q,
  end

@[simp,ematch] private lemma cocone_map_composed_with_morphism_from_initial_object
  {j : J}
    : (M.initial_object.cocone_maps j) ≫ (M.morphism_from_initial_object_to Y).cocone_morphism = Y.cocone_maps j :=
  (M.morphism_from_initial_object_to Y).commutativity j

@[applicable] definition morphism_from_initial_object_cocone_point 
  {Z : C}
  (cocone_maps : Π j : J, Hom (F.onObjects j) Z) 
  (commutativity : Π j k : J, Π f : Hom j k, (F.onMorphisms f) ≫ (cocone_maps k) = cocone_maps j)
   : Hom M.initial_object.cocone_point Z :=
begin
  let cocone : Cocone F := {
    cocone_point  := Z,
    cocone_maps   := cocone_maps,
    commutativity := commutativity
 },
  exact (M.morphism_from_initial_object_to cocone).cocone_morphism, 
end

end categories.universal.lemmas.limit_functoriality
