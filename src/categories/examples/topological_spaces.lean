import ..category
import analysis.topology.topological_space
import analysis.topology.continuity

open categories

namespace categories.examples.topological_spaces

structure morphism {α β : Type } (t : topological_space α) (s : topological_space β) :=
(map : α → β)
(continuity : continuous map)

instance morphism_to_map { α β : Type } { s : topological_space α } { t : topological_space β } : has_coe_to_fun (morphism s t) :=
{ F   := λ f, Π x : α, β,
coe := morphism.map }

def compose { α β γ : Type } { s : topological_space α } { t : topological_space β } { u : topological_space γ}
( f: morphism s t ) ( g: morphism t u )  : morphism s u :=
{  
  map        := λ x, g (f x),
  continuity := continuous_compose f.continuity g.continuity
}

local notation g ∘ f := compose f g
local attribute [simp] compose

def identity { α : Type } ( t : topological_space α ) : morphism t t := ⟨ id, continuous_id ⟩

@[simp] lemma id_value { α : Type } ( t : topological_space α ) (x : α) : identity t x = x := rfl

lemma left_identity { α β : Type } { s : topological_space α } { t : topological_space β }
( f: morphism s t ) : (identity t) ∘ f = f := by cases f; simp; refl

lemma right_identity { α β : Type } { s : topological_space α } { t : topological_space β }
( f: morphism s t ) : f ∘ (identity s) = f := by cases f; simp; refl

lemma associativity {α β γ δ : Type } {t : topological_space α} {s : topological_space β} {u : topological_space γ} {v : topological_space δ}
(f : morphism s t) (g : morphism t u) (h : morphism u v) : h ∘ (g ∘ f) = (h ∘ g) ∘ f := by simp ; refl

def Top : Category :=
{
  Obj            := Σ α : Type, topological_space α,
  Hom            := λ X Y, morphism X.2 Y.2,
  identity       := λ X, identity X.2,
  compose        := λ _ _ _ f g, compose f g,
  left_identity  := λ _ _, left_identity,
  right_identity := λ _ _, right_identity,
  associativity  := λ _ _ _ _, associativity,
}


local attribute [applicable] set.subset.refl

structure OpenSets { α } ( X : topological_space α ) := 
 ( underlying_set : set α )
 ( is_open : X.is_open underlying_set )

attribute [applicable] OpenSets.is_open

local attribute [applicable] topological_space.is_open_inter

instance OpenSets.has_inter { α } { X : topological_space α } : has_inter (OpenSets X) := {
  inter := λ U V, ⟨ U.underlying_set ∩ V.underlying_set, ♯ ⟩ 
}
instance OpenSets.has_subset { α } { X : topological_space α } : has_subset (OpenSets X) := {
  subset := λ U V, U.underlying_set ⊆ V.underlying_set
}

def topological_space.to_category { α : Type } ( X : topological_space α ) : Category :=
{
  Obj            := OpenSets X,
  Hom            := λ U V, plift (U ⊆ V),
  identity       := ♯,
  compose        := λ _ _ _ f g, begin tidy, apply set.subset.trans f g end,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

instance topological_space.to_category.has_inter { α } ( X : topological_space α )  : has_inter ((topological_space.to_category X).Obj)  := OpenSets.has_inter 
instance topological_space.to_category.has_subset { α } ( X : topological_space α ) : has_subset ((topological_space.to_category X).Obj) := OpenSets.has_subset

end categories.examples.topological_spaces