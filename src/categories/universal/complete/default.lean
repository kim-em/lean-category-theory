-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..instances
import ...discrete_category
import ...opposites
import .lemmas.limit_functoriality

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.isomorphism
open categories.products
open categories.initial
open categories.types
open categories.util

namespace categories.universal

universes u₁ u₂ u₃ u₄ 

class Complete_for (C : Category.{u₁ u₂}) (p : Category.{u₃ u₄} → Prop) := 
  (limitCone : Π {J : Category.{u₃ u₄}} (w : p J) (F : Functor J C), LimitCone F)

class Complete (C : Category.{u₁ u₂}) := 
  (limitCone : Π {J : Category.{u₃ u₄}} (F : Functor J C), LimitCone F)

definition limitCone {C : Category.{u₁ u₂}} [Complete.{u₁ u₂ u₃ u₄} C] {J : Category.{u₃ u₄}} (F : Functor J C) := Complete.limitCone F
definition limit     {C : Category.{u₁ u₂}} [Complete.{u₁ u₂ u₃ u₄} C] {J : Category.{u₃ u₄}} (F : Functor J C) := (Complete.limitCone F).terminal_object.cone_point

class Cocomplete_for (C : Category.{u₁ u₂}) (p : Category.{u₃ u₄} → Prop) := 
  (colimitCocone : Π {J : Category.{u₃ u₄}} (w : p J) (F : Functor J C), ColimitCocone F)

class Cocomplete (C : Category.{u₁ u₂}) := 
  (colimitCocone : Π {J : Category.{u₃ u₄}} (F : Functor J C), ColimitCocone F)

definition {u v} colimitCocone {C : Category.{u₁ u₂}} [Cocomplete.{u₁ u₂ u₃ u₄} C] {J : Category.{u₃ u₄}} (F : Functor J C) := Cocomplete.colimitCocone F
definition {u v} colimit       {C : Category.{u₁ u₂}} [Cocomplete.{u₁ u₂ u₃ u₄} C] {J : Category.{u₃ u₄}} (F : Functor J C) := (Cocomplete.colimitCocone F).initial_object.cocone_point

open categories.universal.lemmas.limit_functoriality

definition Limit {J : Category} {C : Category} [Complete C] : Functor (FunctorCategory J C) C := {
  onObjects     := λ F, (limitCone F).terminal_object.cone_point,
  onMorphisms   := λ F G τ, let lim_F := (limitCone F) in
                            let lim_G := (limitCone G) in
                              (lim_G.morphism_to_terminal_object_from {
                                cone_point    := _,
                                cone_maps     := (λ j, C.compose (lim_F.terminal_object.cone_maps j) (τ.components j))
                             }).cone_morphism
}

open categories.opposites

definition Colimit {J : Category} {C : Category} [Cocomplete C] : Functor (FunctorCategory J C) C := {
  onObjects     := λ F, (colimitCocone F).initial_object.cocone_point,
  onMorphisms   := λ F G τ, let colim_F := (colimitCocone F) in
                            let colim_G := (colimitCocone G) in
                              (colim_F.morphism_from_initial_object_to {
                                cocone_point    := _,
                                cocone_maps     := (λ j, C.compose (τ.components j) (colim_G.initial_object.cocone_maps j))
                             }).cocone_morphism
}

end categories.universal