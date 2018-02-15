-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .currying_1

open categories
open categories.isomorphism
open categories.functor
open categories.equivalence

namespace categories.natural_transformation

universes u₁ u₂ u₃

variables (C : Type u₁) (D : Type u₂) (E : Type u₃)
variables [category C] [category D] [category E]

local attribute [applicable] category.identity -- this is usually a bad idea, but just what we needed here

definition Curry_Uncurry_to_identity
    : NaturalTransformation (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) (IdentityFunctor _) := ♯ 

definition identity_to_Curry_Uncurry
    : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) := ♯ 

definition Uncurry_Curry_to_identity
    : NaturalTransformation (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) (IdentityFunctor _) := ♯ 
     
definition identity_to_Uncurry_Curry
    : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) := ♯ 

end categories.natural_transformation