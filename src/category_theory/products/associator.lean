-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.products
import category_theory.equivalence

open category_theory

namespace category_theory.prod

universes u₁ v₁ u₂ v₂ u₃ v₃
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C] (D : Type u₂) [𝒟 : category.{u₂ v₂} D] (E : Type u₃) [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

local attribute [tidy] tactic.assumption

def associator : ((C × D) × E) ⥤ (C × (D × E)) := by tidy
-- { obj := λ X, (X.1.1, (X.1.2, X.2)),
--   map := λ _ _ f, (f.1.1, (f.1.2, f.2)) }

-- @[simp] lemma associator_obj (X) : (associator C D E) X = (X.1.1, (X.1.2, X.2)) := rfl
-- @[simp] lemma associator_map {X Y} (f : X ⟶ Y) : (associator C D E).map f = (f.1.1, (f.1.2, f.2)) := rfl

def inverse_associator : (C × (D × E)) ⥤ ((C × D) × E) := by tidy
-- { obj := λ X, ((X.1, X.2.1), X.2.2),
--   map := λ _ _ f, ((f.1, f.2.1), f.2.2) }

-- @[simp] lemma inverse_associator_obj (X) : (inverse_associator C D E) X = ((X.1, X.2.1), X.2.2) := rfl
-- @[simp] lemma inverse_associator_map {X Y} (f : X ⟶ Y) : (inverse_associator C D E).map f = ((f.1, f.2.1), f.2.2) := rfl

local attribute [back] category.id

def associativity : equivalence ((C × D) × E) (C × (D × E)) := --by obviously -- times out
{ functor := associator C D E,
  inverse := inverse_associator C D E, }

-- TODO pentagon natural transformation? satisfying?

end category_theory.prod
