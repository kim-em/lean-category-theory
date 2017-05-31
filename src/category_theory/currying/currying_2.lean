-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .currying_1

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor
open tqft.categories.equivalence

namespace tqft.categories.natural_transformation

definition {u1 v1 u2 v2 u3 v3} Curry_Uncurry_to_identity
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} )  : NaturalTransformation (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) (IdentityFunctor _) :=
      {
         components := λ F, {
             components := λ X, {
                 components := λ Y, E.identity ((F.onObjects X).onObjects Y),
                 naturality := ♯
             },
             naturality := begin
                             intros, 
                             pointwise, 
                             intros, 
                             unfold_projections, 
                             simp, 
                             unfold_projections, 
                             simp, 
                             dsimp, 
                             erewrite Category.left_identity,  -- PROJECT why are these necessary? PROJECT automation
                             erewrite Category.right_identity,
                           end
         },
         naturality := begin
                         intros, 
                         pointwise, 
                         intros, 
                         unfold_projections, 
                         pointwise, 
                         intros, 
                         simp, 
                         unfold_projections, 
                         dsimp, 
                         erewrite Category.left_identity,  -- PROJECT why are these necessary? PROJECT automation
                         erewrite Category.right_identity,
                       end
     }
definition {u1 v1 u2 v2 u3 v3} identity_to_Curry_Uncurry
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} )  : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) :=
      {
         components := λ F, {
             components := λ X, {
                 components := λ Y, E.identity ((F.onObjects X).onObjects Y),
                 naturality := ♯
             },
             naturality := begin
                             intros, 
                             pointwise, 
                             intros, 
                             unfold_projections, 
                             simp, 
                             unfold_projections, 
                             simp, 
                             dsimp, 
                             erewrite Category.left_identity,  -- PROJECT why are these necessary? PROJECT automation
                             erewrite Category.right_identity,
                           end
         },
         naturality := begin
                         intros, 
                         pointwise, 
                         intros, 
                         unfold_projections, 
                         pointwise, 
                         intros, 
                         simp, 
                         unfold_projections, 
                         dsimp, 
                         erewrite Category.left_identity,  -- PROJECT why are these necessary? PROJECT automation
                         erewrite Category.right_identity,
                       end
     }

@[simp] lemma { u v } congr_arg_refl { α : Type u } { β : Type v } ( f : α → β ) ( a : α ) : congr_arg f (eq.refl a) = eq.refl (f a) :=
begin
  refl
end
@[simp] lemma { u v } congr_refl_refl { α : Type u } { β : Type v } ( f : α → β ) ( a : α ) : congr (eq.refl f) (eq.refl a) = eq.refl (f a) :=
begin
  refl
end
@[simp] lemma { u v } mpr_refl { α : Type u } ( h : α = α ) ( a : α ) : eq.mpr h a = a :=
begin
  refl
end


definition {u1 v1 u2 v2 u3 v3} Uncurry_Curry_to_identity
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} )  : NaturalTransformation (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) (IdentityFunctor _) :=
      {
         components := λ (F: Functor (C × D) E), {
             components := λ X, begin
                                  unfold_projections,
                                  simp,
                                  unfold_projections,
                                  simp,
                                  exact (E.identity (F.onObjects X))
                                end,
             naturality := begin
                             intros, 
                             unfold_projections, 
                             simp, 
                             unfold_projections, 
                             simp, 
                             dsimp, 
                             induction f with f_1 f_2,
                             induction X with X_1 X_2,
                             induction Y with Y_1 Y_2,
                             dsimp,
                             erewrite E.left_identity,
                             erewrite E.right_identity,
                           end
         },
         naturality := begin 
                         intros F G τ,
                         pointwise,
                         intros X,
                         unfold_projections,
                         simp,
                         dsimp,
                         unfold_projections,
                         simp,
                         dsimp,
                         induction X with X_1 X_2,
                         dsimp,
                         unfold pair_equality,
                         dsimp,
                         repeat { rewrite congr_arg_refl },
                         repeat { rewrite congr_refl_refl },
                         dsimp [eq.mpr],
                         simp,
                       end
     }
definition {u1 v1 u2 v2 u3 v3} identity_to_Uncurry_Curry
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} )  : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) :=
      {
         components := λ (F: Functor (C × D) E), {
             components := λ X, begin
                                  unfold_projections,
                                  simp,
                                  unfold_projections,
                                  simp,
                                  exact (E.identity (F.onObjects X))
                                end,
             naturality := begin
                             intros, 
                             unfold_projections, 
                             simp, 
                             unfold_projections, 
                             simp, 
                             dsimp, 
                             induction f with f_1 f_2,
                             induction X with X_1 X_2,
                             induction Y with Y_1 Y_2,
                             dsimp,
                             erewrite E.left_identity,
                             erewrite E.right_identity,
                           end
         },
         naturality := begin 
                         intros F G τ,
                         pointwise,
                         intros X,
                         unfold_projections,
                         simp,
                         dsimp,
                         unfold_projections,
                         simp,
                         dsimp,
                         induction X with X_1 X_2,
                         dsimp,
                         unfold pair_equality,
                         dsimp,
                         repeat { rewrite congr_arg_refl },
                         repeat { rewrite congr_refl_refl },
                         dsimp [eq.mpr],
                         simp,
                       end
     }

end tqft.categories.natural_transformation