-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.instances
import category_theory.discrete_category
import category_theory.opposites
import category_theory.universal.complete.lemmas.limit_functoriality

open category_theory
open category_theory.initial

namespace category_theory.universal

universes u₁ u₂ 

class Complete (C : Type (u₁+1)) [large_category C] := 
  (limitCone : Π {J : Type u₁} [small_category J] (F : J ↝ C), LimitCone F)

class Cocomplete (C : Type (u₁+1)) [large_category C] := 
  (colimitCocone : Π {J : Type u₁} [small_category J] (F : J ↝ C), ColimitCocone F)

variable {C : Type (u₁+1)}
variable [large_category C]
variable {J : Type u₁}
variables [small_category J]

def limitCone [Complete C] (F : J ↝ C) := Complete.limitCone F
def limit     [Complete C] (F : J ↝ C) := (Complete.limitCone F).obj.cone_point

def colimitCocone [Cocomplete C] (F : J ↝ C) := Cocomplete.colimitCocone F
def colimit       [Cocomplete C] (F : J ↝ C) := (Cocomplete.colimitCocone F).obj.cocone_point

open category_theory.universal.lemmas.limit_functoriality

def functorial_Limit [Complete C] : (J ↝ C) ↝ C := 
{ obj := λ F, (limitCone F).obj.cone_point,
  map' := λ F G τ, let lim_F := (limitCone F) in
                  let lim_G := (limitCone G) in
                    (lim_G.«from» { cone_point := _,
                                    cone_maps  := (λ j, (lim_F.obj.cone_maps j) ≫ (τ j)) }).cone_morphism }

def functorial_Colimit [Cocomplete C] : (J ↝ C) ↝ C := 
{ obj := λ F, (colimitCocone F).obj.cocone_point,
  map' := λ F G τ, let colim_F := (colimitCocone F) in
                  let colim_G := (colimitCocone G) in
                    (colim_F.to { cocone_point := _,
                                  cocone_maps  := (λ j, (τ j) ≫ (colim_G.obj.cocone_maps j)) }).cocone_morphism }

end category_theory.universal