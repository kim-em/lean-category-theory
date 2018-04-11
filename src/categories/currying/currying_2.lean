-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.currying.currying_1

open categories
open categories.isomorphism
open categories.functor
open categories.equivalence

namespace categories.natural_transformation

universes u₁ u₂ u₃

variables (C : Type (u₁+1)) [category C] (D : Type (u₂+1)) [category D] (E : Type (u₃+1)) [category E]

local attribute [applicable] category.identity -- this is usually a bad idea, but just what we needed here

definition Curry_Uncurry_to_identity
    : ((Uncurry_Functors C D E) ⋙ (Curry_Functors C D E)) ⟹ 1 := by obviously 

definition identity_to_Curry_Uncurry
    : 1 ⟹ ((Uncurry_Functors C D E) ⋙ (Curry_Functors C D E)) := by obviously 

definition Uncurry_Curry_to_identity
    : ((Curry_Functors C D E) ⋙ (Uncurry_Functors C D E)) ⟹ 1 := by obviously 
     
definition identity_to_Uncurry_Curry
    : 1 ⟹ ((Curry_Functors C D E) ⋙ (Uncurry_Functors C D E)) := by obviously 

end categories.natural_transformation