-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..functor
import .semigroups

namespace tqft.categories.examples.monoids

open tqft.categories

set_option pp.universes true

structure monoid_morphism { α β : Type } ( s : monoid α ) ( t: monoid β ) :=
  (map: α → β)
  (multiplicative : ∀ x y : α, map(x * y) = map(x) * map(y))
  (unital : map(one) = one)

attribute [simp] monoid_morphism.multiplicative
attribute [simp] monoid_morphism.unital

-- This defines a coercion so we can write `f x` for `map f x`.
instance monoid_morphism_to_map { α β : Type } { s : monoid α } { t: monoid β } : has_coe_to_fun (monoid_morphism s t) :=
{ F   := λ f, Π x : α, β,
  coe := monoid_morphism.map }

definition monoid_identity { α : Type } ( s: monoid α ) : monoid_morphism s s := ⟨ id, ♮, ♮ ⟩

definition monoid_morphism_composition
  { α β γ : Type } { s: monoid α } { t: monoid β } { u: monoid γ}
  ( f: monoid_morphism s t ) ( g: monoid_morphism t u ) : monoid_morphism s u :=
{
  map := λ x, g (f x),
  multiplicative := ♮,
  unital := ♮
}

@[pointwise] lemma monoid_morphism_pointwise_equality
  { α β : Type } { s : monoid α } { t: monoid β }
  ( f g : monoid_morphism s t )
  ( w : ∀ x : α, f x = g x) : f = g :=
/-
-- This proof is identical to that of the lemma NaturalTransformations_componentwise_equal.
-- TODO: automate!
-/
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc, from funext w,
    by subst hc
end

definition CategoryOfMonoids : Category := 
{
    Obj := Σ α : Type, monoid α,
    Hom := λ s t, monoid_morphism s.2 t.2,

    identity := λ s, monoid_identity s.2,
    compose  := λ _ _ _ f g, monoid_morphism_composition f g,

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

open tqft.categories.functor
open tqft.categories.examples.semigroups

-- Sadly doesn't work:
-- definition cast_monoid_to_semigroup' {α: Type} (s: monoid α) : semigroup α := s
definition cast_monoid_to_semigroup {α: Type} (s: monoid α) : semigroup α := @monoid.to_semigroup α s

definition ForgetfulFunctor_Monoids_to_Semigroups : Functor CategoryOfMonoids CategoryOfSemigroups :=
{
  onObjects     := λ s, sigma.mk s.1 (@monoid.to_semigroup s.1 s.2),
  onMorphisms   := λ s t, λ f : monoid_morphism s.2 t.2, 
                  {
                    map            := f^.map,
                    multiplicative := f^.multiplicative
                  },

  identities    := ♮,
  functoriality := ♮
}

end tqft.categories.examples.monoids
