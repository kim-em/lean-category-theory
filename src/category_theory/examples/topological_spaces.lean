-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison

import category_theory.full_subcategory
import category_theory.opposites
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

variables {α : Type u₁} (X : topological_space α) 

structure Open : Type u₁ := 
(s : set α)
(is_open : X.is_open s)

instance : has_coe (Open X) (set α) := {coe := λ U, U.s }

attribute [back] Open.is_open
local attribute [back] topological_space.is_open_inter

instance : has_inter (Open X) := 
{ inter := λ U V, ⟨ U.s ∩ V.s, by obviously ⟩ }

instance has_inter_op : has_inter ((Open X)ᵒᵖ) := 
{ inter := λ U V, ⟨ U.s ∩ V.s, by obviously ⟩ }

instance : has_subset (Open X) := 
{ subset := λ U V, U.s ⊆ V.s }

instance : has_mem α (Open X) := 
{ mem := λ a V, a ∈ V.s }

instance [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := by tidy,
  comp := begin tidy, transitivity Y; assumption end } -- automate, via mono?

instance : preorder (Open X) :=
begin
  refine { le := (⊆), .. } ; tidy
end

instance open_sets : small_category (Open X) := by apply_instance

def nbhd {α} [X : topological_space α] (x : α) := { U : Open X // x ∈ U }
def nbhds {α} [X : topological_space α] (x : α) : small_category (nbhd x) := begin unfold nbhd, apply_instance end

end category_theory.examples.topological_spaces
