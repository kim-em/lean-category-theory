-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.functor
import .semigroups

namespace categories.examples.monoids

open categories

structure monoid_morphism { α β : Type } ( s : monoid α ) ( t : monoid β ) :=
  ( map: α → β )
  ( multiplicative : ∀ x y : α, map (monoid.mul x y) = monoid.mul (map x) (map y) . tidy' )
  ( unital : map(s.one) = t.one . tidy' )

make_lemma monoid_morphism.multiplicative
make_lemma monoid_morphism.unital
attribute [simp] monoid_morphism.multiplicative_lemma monoid_morphism.unital_lemma

-- This defines a coercion so we can write `f x` for `map f x`.
instance monoid_morphism_to_map { α β : Type } { s : monoid α } { t : monoid β } : has_coe_to_fun (monoid_morphism s t) :=
{ F   := λ f, Π x : α, β,
  coe := monoid_morphism.map }

definition monoid_identity { α : Type } ( s : monoid α ) : monoid_morphism s s := ⟨ id, ♯, ♯  ⟩

definition monoid_morphism_composition
  { α β γ : Type } { s : monoid α } { t : monoid β } { u : monoid γ}
  ( f: monoid_morphism s t ) ( g: monoid_morphism t u ) : monoid_morphism s u :=
{
  map := λ x, g (f x)
}

@[applicable] lemma monoid_morphism_pointwise_equality
  { α β : Type } { s : monoid α } { t : monoid β }
  ( f g : monoid_morphism s t )
  ( w : ∀ x : α, f x = g x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc := funext w,
    subst hc
end

definition CategoryOfMonoids : Category := 
{
    Obj := Σ α : Type, monoid α,
    Hom := λ s t, monoid_morphism s.2 t.2,

    identity := λ s, monoid_identity s.2,
    compose  := λ _ _ _ f g, monoid_morphism_composition f g
}

open categories.functor
open categories.examples.semigroups

definition ForgetfulFunctor_Monoids_to_Semigroups : Functor CategoryOfMonoids CategoryOfSemigroups :=
{
  onObjects     := λ s, ⟨ s.1, @monoid.to_semigroup s.1 s.2 ⟩,
  onMorphisms   := λ s t, λ f : monoid_morphism s.2 t.2, 
                  {
                    map            := f.map,
                    multiplicative := f.multiplicative
                  }
}

end categories.examples.monoids
