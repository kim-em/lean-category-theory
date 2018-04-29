-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.small_category
import categories.universal.instances
import categories.discrete_category
import categories.opposites
import categories.universal.complete.lemmas.limit_functoriality

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.isomorphism
open categories.products
open categories.initial
open categories.types

namespace categories.universal

universes u₁ u₂ 
variable {C : Type (u₁+1)}
variable [category C]

class Complete (C : Type (u₁+1)) [category C] := 
  (limitCone : Π {J : Type (u₁+1)} [small J] [category J] (F : J ↝ C), LimitCone F)

class Cocomplete (C : Type (u₁+1)) [category C] := 
  (colimitCocone : Π {J : Type (u₁+1)} [small J] [category J] (F : J ↝ C), ColimitCocone F)

variable {J : Type (u₁+1)}
variables [small J] [category J]

definition limitCone [Complete C] (F : J ↝ C) := Complete.limitCone F
definition limit     [Complete C] (F : J ↝ C) := (Complete.limitCone F).terminal_object.cone_point

definition colimitCocone [Cocomplete C] (F : J ↝ C) := Cocomplete.colimitCocone F
definition colimit       [Cocomplete C] (F : J ↝ C) := (Cocomplete.colimitCocone F).initial_object.cocone_point

open categories.universal.lemmas.limit_functoriality

definition functorial_Limit [Complete C] : (J ↝ C) ↝ C := {
  onObjects     := λ F, (limitCone F).terminal_object.cone_point,
  onMorphisms   := λ F G τ, let lim_F := (limitCone F) in
                            let lim_G := (limitCone G) in
                              (lim_G.morphism_to_terminal_object_from {
                                cone_point    := _,
                                cone_maps     := (λ j, (lim_F.terminal_object.cone_maps j) ≫ (τ.components j))
                             }).cone_morphism
}

open categories.opposites

definition functorial_Colimit [Cocomplete C] : (J ↝ C) ↝ C := {
  onObjects     := λ F, (colimitCocone F).initial_object.cocone_point,
  onMorphisms   := λ F G τ, let colim_F := (colimitCocone F) in
                            let colim_G := (colimitCocone G) in
                              (colim_F.morphism_from_initial_object_to {
                                cocone_point    := _,
                                cocone_maps     := (λ j, (τ.components j) ≫ (colim_G.initial_object.cocone_maps j))
                             }).cocone_morphism
}

end categories.universal