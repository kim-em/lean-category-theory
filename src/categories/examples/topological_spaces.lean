-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison

import ..category
import analysis.topology.topological_space
import analysis.topology.continuity

open categories

namespace categories.examples.topological_spaces

structure morphism {α β : Type } (t : topological_space α) (s : topological_space β) :=
(map : α → β)
(continuity : continuous map)

@[applicable] lemma morphism_pointwise_equality
  { α β : Type } { s : topological_space α } { t: topological_space β }
  ( f g : morphism s t )
  ( w : ∀ x : α, f.map x = g.map x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc := funext w,
    subst hc
end

instance morphism_to_map { α β : Type } { s : topological_space α } { t : topological_space β } : has_coe_to_fun (morphism s t) :=
{ F   := λ f, Π x : α, β,
coe := morphism.map }

def compose { α β γ : Type } { s : topological_space α } { t : topological_space β } { u : topological_space γ}
( f: morphism s t ) ( g: morphism t u )  : morphism s u :=
{  
  map        := λ x, g (f x),
  continuity := continuous.comp f.continuity g.continuity
}

local notation g ∘ f := compose f g
local attribute [simp] compose

def identity { α : Type } ( t : topological_space α ) : morphism t t := ⟨ id, continuous_id ⟩

@[simp] lemma id_value { α : Type } ( t : topological_space α ) (x : α) : identity t x = x := rfl

def Top : Category :=
{
  Obj            := Σ α : Type, topological_space α,
  Hom            := λ X Y, morphism X.2 Y.2,
  identity       := λ X, identity X.2,
  compose        := λ _ _ _ f g, compose f g
}


local attribute [applicable] set.subset.refl

structure OpenSet { α } ( X : topological_space α ) := 
 ( underlying_set : set α )
 ( is_open : X.is_open underlying_set )

attribute [applicable] OpenSet.is_open

local attribute [applicable] topological_space.is_open_inter

instance OpenSet.has_inter { α } { X : topological_space α } : has_inter (OpenSet X) := {
  inter := λ U V, ⟨ U.underlying_set ∩ V.underlying_set, ♯ ⟩ 
}
instance OpenSet.has_subset { α } { X : topological_space α } : has_subset (OpenSet X) := {
  subset := λ U V, U.underlying_set ⊆ V.underlying_set
}
instance OpenSet.mem { α } { X : topological_space α } : has_mem α (OpenSet X) := {
  mem := λ a V, a ∈ V.underlying_set
}

def topological_space.to_category { α : Type } ( X : topological_space α ) : Category :=
{
  Obj            := OpenSet X,
  Hom            := λ U V, plift (U ⊆ V),
  identity       := ♯,
  compose        := λ _ _ _ f g, begin tidy, apply set.subset.trans f g end
}

instance topological_space.to_category.has_inter { α } ( X : topological_space α )  : has_inter ((topological_space.to_category X).Obj)  := OpenSet.has_inter 
instance topological_space.to_category.has_subset { α } ( X : topological_space α ) : has_subset ((topological_space.to_category X).Obj) := OpenSet.has_subset

end categories.examples.topological_spaces