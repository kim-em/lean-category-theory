-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .currying_1

open categories
open categories.isomorphism
open categories.functor
open categories.equivalence

namespace categories.natural_transformation

definition {u1 v1 u2 v2 u3 v3} Curry_Uncurry_to_identity
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} )  : NaturalTransformation (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) (IdentityFunctor _) :=
      {
         components := λ F, {
             components := --by tidy, -- PROJECT seems to cause problems below
                            λ X, {
                                components := by tidy, --λ Y, E.identity ((F.onObjects X).onObjects Y),
                                naturality := ♯
                            },
             naturality := ♯
         },
         naturality := --♯ -- PROJECT this seems to run forever?
                       begin
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
                 components := by tidy, --λ Y, E.identity ((F.onObjects X).onObjects Y),
                 naturality := ♯
             },
             naturality := ♯
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

definition {u1 v1 u2 v2 u3 v3} Uncurry_Curry_to_identity
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} )  : NaturalTransformation (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) (IdentityFunctor _) := 
  -- PROJECT why can't tidy just do all this itself?
      {
         components := λ (F: Functor (C × D) E), {
             components := by tidy, -- can't write ♯ here because abstract things can't be unfolded
             naturality := ♯ 
         },
         naturality := ♯
     }
     
definition {u1 v1 u2 v2 u3 v3} identity_to_Uncurry_Curry
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} )  : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) :=
      {
         components := λ (F: Functor (C × D) E), {
             components := by tidy, -- can't write ♯ here because abstract things can't be unfolded
             naturality := ♯
         },
         naturality := ♯
     }

end categories.natural_transformation