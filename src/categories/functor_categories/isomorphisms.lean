-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.natural_isomorphism

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ u₂ u₃ u₄

variable {B : Type (u₁+1)}
variable [category B]
variable {C : Type (u₂+1)}
variable [category C]
variable {D : Type (u₃+1)}
variable [category D]
variable {E : Type (u₄+1)}
variable [category E]

local attribute [applicable] uv_category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition FunctorComposition_left_unitor (F : C ↝ D) : (1 ⋙ F) ⇔ F := by obviously

definition FunctorComposition_right_unitor (F : C ↝ D) : (F ⋙ 1) ⇔ F := by obviously

definition FunctorComposition_associator (F : B ↝ C) (G : C ↝ D) (H : D ↝ E) : ((F ⋙ G) ⋙ H) ⇔ (F ⋙ (G ⋙ H)) := by obviously 

-- PROJECT pentagon

end categories.functor_categories
