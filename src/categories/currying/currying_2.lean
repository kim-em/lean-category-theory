-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.currying.currying_1

open categories
open categories.functor

namespace categories.natural_transformation

universes u₁ u₂ v₂ 

variables (C : Type u₁) [small_category C] (D : Type u₁) [small_category D] (E : Type u₂) [ℰ : category.{u₂ v₂} E]
include ℰ

local attribute [applicable] category.identity -- this is usually a bad idea, but just what we needed here
local attribute [tidy] dsimp_all' -- TODO get rid of this

definition Curry_Uncurry_to_identity : ((Uncurry_Functors C D E) ⋙ (Curry_Functors C D E)) ⟹ (IdentityFunctor (C ↝ (D ↝ E))) := by obviously

definition identity_to_Curry_Uncurry
    : (IdentityFunctor (C ↝ (D ↝ E))) ⟹ ((Uncurry_Functors C D E) ⋙ (Curry_Functors C D E)) := by obviously 

definition Uncurry_Curry_to_identity
    : ((Curry_Functors C D E) ⋙ (Uncurry_Functors C D E)) ⟹ (IdentityFunctor ((C × D) ↝ E)) := by obviously 
     
definition identity_to_Uncurry_Curry
    : (IdentityFunctor ((C × D) ↝ E)) ⟹ ((Curry_Functors C D E) ⋙ (Uncurry_Functors C D E)) := by obviously 

end categories.natural_transformation