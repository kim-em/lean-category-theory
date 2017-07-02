-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .instances
import ..discrete_category

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
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

@[pointwise] private lemma {u v} uniqueness_of_morphism_to_limit
  { J C : Category.{u v} }
  { F : Functor J C }
  { L : LimitCone F }
  { X : Cone F }
  { g : C.Hom X.cone_point L.terminal_object.cone_point }
  ( w : ∀ j : J.Obj, C.compose g ((L.terminal_object).cone_maps j) = X.cone_maps j )
    : (L.morphism_to_terminal_object_from X).morphism = g :=
  begin
    let G : (Cones F).Hom X L.terminal_object := ⟨ g, w ⟩,
    have q := L.uniqueness_of_morphisms_to_terminal_object _ (L.morphism_to_terminal_object_from X) G,
    exact congr_arg ConeMorphism.morphism q,
  end

@[simp,ematch] private lemma {u v} morphism_to_terminal_object_composed_with_cone_map
  { J C : Category.{u v} }
  { F : Functor J C }
  { L : LimitCone F }
  { X : Cone F }
  { j : J.Obj }
    : C.compose (L.morphism_to_terminal_object_from X).morphism (L.terminal_object.cone_maps j) = X.cone_maps j :=
  (L.morphism_to_terminal_object_from X).commutativity j

definition {u v} Limit { J C : Category.{u v} } [ Complete C ] : Functor (FunctorCategory J C) C := {
  onObjects     := λ F, (limitCone F).terminal_object.cone_point,
  onMorphisms   := λ F G τ, let lim_F := (limitCone F) in
                            let lim_G := (limitCone G) in
                              (lim_G.morphism_to_terminal_object_from {
                                cone_point    := _,
                                cone_maps     := (λ j, C.compose (lim_F.terminal_object.cone_maps j) (τ.components j)),
                                commutativity := ♯ 
                              }).morphism,
  identities    := ♯,
  functoriality := begin
                     tidy,
                     rewrite C.associativity,
                     simp,
                     rewrite - C.associativity,
                     blast,
                   end
}

private definition evaluate_Functor_to_FunctorCategory { J C D : Category } ( F : Functor J (FunctorCategory C D )) ( c : C.Obj ) : Functor J D := {
  onObjects     := λ j, (F.onObjects j).onObjects c,
  onMorphisms   := λ _ _ f, (F.onMorphisms f).components c,
  identities    := ♯,
  functoriality := ♯ 
}

private definition evaluate_Functor_to_FunctorCategory_on_Morphism { J C D : Category } ( F : Functor J (FunctorCategory C D )) ( c c' : C.Obj ) ( f : C.Hom c c' )
  : NaturalTransformation (evaluate_Functor_to_FunctorCategory F c) (evaluate_Functor_to_FunctorCategory F c') := {
    components := λ j, (F.onObjects j).onMorphisms f,
    naturality := ♯ 
  }

-- PROJECT
-- instance Limits_in_FunctorCategory ( C D : Category ) [ cmp : Complete D ] : Complete (FunctorCategory C D) := {
--   limitCone := λ J F, {
--     object     := {
--       -- TODO the whole definition of limit should come down to the fact that limits are functorial
--       limit         := {
--         onObjects     := λ c, limit (evaluate_Functor_to_FunctorCategory F c),
--         onMorphisms   := λ c c' f, sorry,
--         identities    := sorry,
--         functoriality := sorry
--       },
--       maps          := sorry,
--       commutativity := sorry
--     },
--     morphisms  := sorry,
--     uniqueness := sorry
--   }
-- }

end categories.universal