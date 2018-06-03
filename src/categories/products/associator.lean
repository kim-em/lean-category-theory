-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.products
import categories.equivalence

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

universes u₁ v₁ u₂ v₂ u₃ v₃
variable (C : Type u₁)
variable [𝒞 : category.{u₁ v₁} C]
variable (D : Type u₂)
variable [𝒟 : category.{u₂ v₂} D]
variable (E : Type u₃)
variable [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

-- PROJECT; by aggressively allowing "assumption" we could do this completely automatically
-- locally tag "assumption" with @[tidy]?
-- or define an aggressive version of tidy (perhaps "follow_your_nose"?)
definition ProductCategoryAssociator : ((C × D) × E) ↝ (C × (D × E)) :=
{ onObjects     := λ X, (X.1.1, (X.1.2, X.2)),
  onMorphisms   := λ _ _ f, (f.1.1, (f.1.2, f.2)) }

definition ProductCategoryInverseAssociator : (C × (D × E)) ↝ ((C × D) × E) :=
{ onObjects     := λ X, ((X.1, X.2.1), X.2.2),
  onMorphisms   := λ _ _ f, ((f.1, f.2.1), f.2.2) }


-- TODO prove the equivalence
-- open categories.equivalence

-- definition ProductCategoryAssociativity : Equivalence ((C × D) × E) (C × (D × E)) :=
-- { functor := ProductCategoryAssociator C D E,
--   inverse := ProductCategoryInverseAssociator C D E, }

-- TODO pentagon natural transformation? satisfying?

end categories.products
