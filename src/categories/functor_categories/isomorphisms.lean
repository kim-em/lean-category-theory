-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.natural_isomorphism

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ 

variable {B : Type u₁}
variable [ℬ : category.{u₁ v₁} B]
variable {C : Type u₂}
variable [𝒞 : category.{u₂ v₂} C]
include ℬ 𝒞

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition FunctorComposition_left_unitor (F : B ↝ C) : (1 ⋙ F) ⇔ F := 
begin
obviously,
-- -- obviously'
-- simplify_proof fsplit,
-- simplify_proof fsplit,
-- simplify_proof `[intros],
-- simplify_proof `[apply categories.category.identity],
-- { simplify_proof `[apply_auto_param] },
-- -- obviously',
-- ---
-- fsplit,
-- intros,
-- apply categories.category.identity,
-- { apply_auto_param },
-- ---
-- ---
-- apply categories.natural_transformation.NaturalTransformations_componentwise_equal,
-- intros,
-- dsimp,
-- simp,
-- ---
-- ---
-- apply categories.natural_transformation.NaturalTransformations_componentwise_equal,
-- intros,
-- dsimp,
-- simp,
-- ---
end

set_option pp.proofs true
-- set_option pp.implicit true
#print FunctorComposition_left_unitor

definition FunctorComposition_right_unitor (F : B ↝ C) : (F ⋙ 1) ⇔ F := by obviously

variable {D : Type u₃}
variable [𝒟 : category.{u₃ v₃} D]
variable {E : Type u₄}
variable [ℰ : category.{u₄ v₄} E]
include 𝒟 ℰ 

definition FunctorComposition_associator (F : B ↝ C) (G : C ↝ D) (H : D ↝ E) : ((F ⋙ G) ⋙ H) ⇔ (F ⋙ (G ⋙ H)) := by obviously 

-- PROJECT pentagon

end categories.functor_categories
