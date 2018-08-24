-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison

import category_theory.full_subcategory
import analysis.topology.topological_space
import analysis.topology.continuity

open category_theory

namespace category_theory.examples.topological_spaces

universe variables u₁ u₂ u₃

-- TODO mathlib
local attribute [class] continuous
local attribute [instance] continuous_id

instance continuous_compose {α} [topological_space α] {β} [topological_space β] {γ} [topological_space γ] (f : α → β) [cf: continuous f] (g : β → γ) [cg: continuous g] : continuous (g ∘ f) :=
continuous.comp cf cg

def Top : Type (u₁+1) := Σ α : Type u₁, topological_space α

instance (X : Top) : topological_space X.1 := X.2

def continuous_map (X Y : Top.{u₁}) : Type u₁ := { f : X.1 → Y.1 // continuous f }

instance {X Y} (f : continuous_map X Y) : continuous f.1 := f.2

instance : large_category Top :=
{ hom  := continuous_map,
  id   := λ X, ⟨ id, continuous_id ⟩,
  comp := λ _ _ _ f g, ⟨ g.val ∘ f.val, continuous.comp f.property g.property ⟩ }

structure OpenSet {α : Type u₁} (X : topological_space α) : Type (u₁+1) := 
 (underlying_set : set α)
 (is_open : X.is_open underlying_set)

attribute [back] OpenSet.is_open
local attribute [back] topological_space.is_open_inter

instance OpenSet.has_inter {α : Type u₁} {X : topological_space α} : has_inter (OpenSet X) := {
  inter := λ U V, ⟨ U.underlying_set ∩ V.underlying_set, by obviously ⟩ 
}
instance OpenSet.has_subset {α : Type u₁} {X : topological_space α} : has_subset (OpenSet X) := {
  subset := λ U V, U.underlying_set ⊆ V.underlying_set
}
instance OpenSet.has_mem {α : Type u₁} {X : topological_space α} : has_mem α (OpenSet X) := {
  mem := λ a V, a ∈ V.underlying_set
}

local attribute [back] set.subset.refl
local attribute [back] topological_space.is_open_inter

-- FIXME
instance category_of_open_sets {α : Type u₁} (X : topological_space α) : large_category (OpenSet X) :=
{ hom  := λ U V, ulift (plift (U ⊆ V)),
  id   := by obviously,
  comp := λ _ _ _ f g, begin sorry, /- tidy, apply set.subset.trans f g -/ end,
  id_comp := sorry,
  comp_id := sorry,
  assoc := sorry }

def Neighbourhoods {α} [X : topological_space α] (x : α) : large_category { U : OpenSet X | x ∈ U } := by apply_instance

end category_theory.examples.topological_spaces