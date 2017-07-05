-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..instances
import ...discrete_category
import ...currying.currying_1
import ...products.switch

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

class {u v} Complete_for ( C : Category.{u v} ) ( p : Category.{u v} → Prop ) := 
  ( limitCone : Π { J : Category.{u v} } ( w : p J ) ( F : Functor J C ), LimitCone F )

class {u v} Complete ( C : Category.{u v} ) := 
  ( limitCone : Π { J : Category.{u v} } ( F : Functor J C ), LimitCone F )

definition {u v} limitCone { C : Category.{u v} } [ Complete.{u v} C ] { J : Category.{u v} } ( F : Functor J C ) := Complete.limitCone F
definition {u v} limit     { C : Category.{u v} } [ Complete.{u v} C ] { J : Category.{u v} } ( F : Functor J C ) := (Complete.limitCone F).terminal_object.cone_point

@[applicable] private lemma {u v} uniqueness_of_morphism_to_limit
  { J C : Category.{u v} }
  { F : Functor J C }
  { L : LimitCone F }
  { X : Cone F }
  { g : C.Hom X.cone_point L.terminal_object.cone_point }
  ( w : ∀ j : J.Obj, C.compose g ((L.terminal_object).cone_maps j) = X.cone_maps j )
    : (L.morphism_to_terminal_object_from X).cone_morphism = g :=
  begin
    let G : (Cones F).Hom X L.terminal_object := ⟨ g, w ⟩,
    have q := L.uniqueness_of_morphisms_to_terminal_object _ (L.morphism_to_terminal_object_from X) G,
    exact congr_arg ConeMorphism.cone_morphism q,
  end

@[simp,ematch] private lemma {u v} morphism_to_terminal_object_composed_with_cone_map
  { J C : Category.{u v} }
  { F : Functor J C }
  { L : LimitCone F }
  { X : Cone F }
  { j : J.Obj }
    : C.compose (L.morphism_to_terminal_object_from X).cone_morphism (L.terminal_object.cone_maps j) = X.cone_maps j :=
  (L.morphism_to_terminal_object_from X).commutativity j

@[applicable] lemma morphism_to_terminal_object_cone_point 
  { J D : Category }
  { Z : D.Obj }
  { G : Functor J D }
  { L : LimitCone G }
  ( cone_maps : Π j : J.Obj, D.Hom Z (G.onObjects j) ) 
  ( commutativity : Π j k : J.Obj, Π f : J.Hom j k, D.compose (cone_maps j) (G.onMorphisms f) = cone_maps k )
   : D.Hom Z L.terminal_object.cone_point :=
begin
  let cone : Cone G := {
    cone_point    := Z,
    cone_maps     := cone_maps,
    commutativity := commutativity
  },
  exact (L.morphism_to_terminal_object_from cone).cone_morphism, 
end

definition {u v} Limit { J C : Category.{u v} } [ Complete C ] : Functor (FunctorCategory J C) C := {
  onObjects     := λ F, (limitCone F).terminal_object.cone_point,
  onMorphisms   := λ F G τ, let lim_F := (limitCone F) in
                            let lim_G := (limitCone G) in
                              (lim_G.morphism_to_terminal_object_from {
                                cone_point    := _,
                                cone_maps     := (λ j, C.compose (lim_F.terminal_object.cone_maps j) (τ.components j)),
                                commutativity := ♯ 
                              }).cone_morphism,
  identities    := ♯,
  functoriality := begin
                     tidy,
                    --  rewrite C.associativity,
                    --  simp,
                     rewrite ← C.associativity,
                     blast,
                   end
}

end categories.universal