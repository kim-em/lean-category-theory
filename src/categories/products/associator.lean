-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.products
import categories.equivalence

open category_theory

namespace category_theory.prod

universes u₁ v₁ u₂ v₂ u₃ v₃
variable (C : Type u₁)
variable [𝒞 : category.{u₁ v₁} C]
variable (D : Type u₂)
variable [𝒟 : category.{u₂ v₂} D]
variable (E : Type u₃)
variable [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

local attribute [tidy] tactic.assumption

definition associator : ((C × D) × E) ↝ (C × (D × E)) := by obviously
-- { obj := λ X, (X.1.1, (X.1.2, X.2)),
--   map := λ _ _ f, (f.1.1, (f.1.2, f.2)) }

definition inverse_associator : (C × (D × E)) ↝ ((C × D) × E) := by obviously
-- { obj := λ X, ((X.1, X.2.1), X.2.2),
--   map := λ _ _ f, ((f.1, f.2.1), f.2.2) }

local attribute [backwards] category.id

-- FIXME looping??
-- definition associativity : Equivalence ((C × D) × E) (C × (D × E)) :=
-- { functor := associator C D E,
--   inverse := inverse_associator C D E, }

-- TODO pentagon natural transformation? satisfying?

end category_theory.prod
