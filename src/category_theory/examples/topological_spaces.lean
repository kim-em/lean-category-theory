-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison

import category_theory.full_subcategory
import category_theory.preorder
import analysis.topology.topological_space
import analysis.topology.continuity

open category_theory

namespace category_theory.examples.topological_spaces

universe u₁

def Top : Type (u₁+1) := Σ α : Type u₁, topological_space α

instance (X : Top) : topological_space X.1 := X.2

def continuous_map (X Y : Top.{u₁}) : Type u₁ := { f : X.1 → Y.1 // continuous f }

instance : large_category Top :=
{ hom  := continuous_map,
  id   := λ X, ⟨ id, continuous_id ⟩,
  comp := λ _ _ _ f g, ⟨ g.val ∘ f.val, continuous.comp f.property g.property ⟩ }

structure open_set (α : Type u₁) [X : topological_space α] : Type u₁ := 
(s : set α)
(is_open : topological_space.is_open X s)

variables {α : Type u₁} [topological_space α]

instance : has_coe (open_set α) (set α) := { coe := λ U, U.s }

instance : has_subset (open_set α) := 
{ subset := λ U V, U.s ⊆ V.s }

instance : preorder (open_set α) := by refine { le := (⊆), .. } ; tidy

instance open_sets : small_category (open_set α) := by apply_instance

instance : has_mem α (open_set α) := 
{ mem := λ a V, a ∈ V.s }

def nbhd (x : α) := { U : open_set α // x ∈ U }
def nbhds (x : α) : small_category (nbhd x) := begin unfold nbhd, apply_instance end

end category_theory.examples.topological_spaces
