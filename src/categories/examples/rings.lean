-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.functor
import .monoids
import ..universal.strongly_concrete
import tactic.ring

namespace categories.examples.rings

open categories
open categories.examples.monoids

structure ring_morphism { α β : Type } ( s : ring α ) ( t : ring β ) :=
  ( map: α → β )
  ( multiplicative : ∀ x y : α, map (ring.mul x y) = ring.mul (map x) (map y) . tidy' )
  ( unital : map(s.one) = t.one . tidy' )
  ( additive : ∀ x y : α, map (ring.add x y) = ring.add (map x) (map y) . tidy' )

make_lemma ring_morphism.multiplicative
make_lemma ring_morphism.unital
make_lemma ring_morphism.additive
attribute [simp] ring_morphism.multiplicative_lemma ring_morphism.unital_lemma ring_morphism.additive_lemma

-- This defines a coercion so we can write `f x` for `map f x`.
instance ring_morphism_to_map { α β : Type } { s : ring α } { t : ring β } : has_coe_to_fun (ring_morphism s t) :=
{ F   := λ f, Π x : α, β,
  coe := λ r, r.map }

definition ring_identity { α : Type } ( s : ring α ) : ring_morphism s s := {
  map := id
}

definition ring_morphism_composition
  { α β γ : Type } { s : ring α } { t : ring β } { u : ring γ}
  ( f: ring_morphism s t ) ( g: ring_morphism t u ) : ring_morphism s u :=
{
  map := λ x, g (f x)
}

@[applicable] lemma ring_morphism_pointwise_equality
  { α β : Type } { s : ring α } { t : ring β }
  ( f g : ring_morphism s t )
  ( w : ∀ x : α, f x = g x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc := funext w,
    subst hc
end

definition CategoryOfRings : Category := 
{
    Obj := Σ α : Type, ring α,
    Hom := λ s t, ring_morphism s.2 t.2,

    identity := λ s, ring_identity s.2,
    compose  := λ _ _ _ f g, ring_morphism_composition f g
}

open categories.functor
open categories.examples.semigroups

definition ForgetfulFunctor_Rings_to_Monoids : Functor CategoryOfRings CategoryOfMonoids :=
{
  onObjects     := λ s, ⟨ s.1, @ring.to_monoid s.1 s.2 ⟩,
  onMorphisms   := λ s t, λ f : ring_morphism s.2 t.2, 
                  {
                    map            := f.map
                  }
}

open categories.types

definition ForgetfulFunctor_Rings_to_Types : Functor CategoryOfRings CategoryOfTypes :=
{
    onObjects   := λ r, r.1,
    onMorphisms := λ _ _ f, f.map 
  }

definition Rings_Concrete : Concrete CategoryOfRings := {
  F := ForgetfulFunctor_Rings_to_Types
}
attribute [instance] Rings_Concrete

structure polynomial (α) [ring α] :=
  ( coefficients : list α )
  ( leading_term_nonzero : ¬(coefficients.nth 0 = some 0) )

open list

definition trim {α} [ring α] [decidable_eq α] : list α → polynomial α
| []       := ⟨ nil, sorry ⟩ 
| (a :: t) := if h : a = 0 then trim t else ⟨ a :: t, sorry ⟩ 

definition polynomial_ring {α} [ring α] [decidable_eq α] : ring (polynomial α) := {
  zero := trim [],
  one := trim [1],
  add := sorry,
  neg := sorry,
  mul := sorry,
  add_zero := sorry,
  zero_add := sorry,
  add_comm := sorry,
  add_assoc := sorry,
  add_left_neg := sorry,
  one_mul := sorry,
  mul_one := sorry,
  mul_assoc := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
}

open categories.yoneda

local attribute [tidy] ring


-- instance Monoids_ForgetfulFunctor_Representable : Representable (ForgetfulFunctor_Monoids_to_Types) := {
--   c := ⟨ ℕ, ℕ_as_monoid_under_addition ⟩,
--   Φ := {
--     morphism := {
--       components := λ r a, {
--         map := λ n, @monoid.pow r.1 r.2 a n,
--       },
--     },
--     inverse := {
--       components := λ r f, f.map 1
--     }
--   }
-- }

-- open categories.universal

-- instance Monoids_StronglyConcrete : StronglyConcrete CategoryOfMonoids := {
--   F := ForgetfulFunctor_Monoids_to_Types,
--   reflects_isos := {
--     reflects := λ X Y f w, {
--       inverse := {
--         map := w.inverse,
--         multiplicative := sorry,
--         unital := sorry
--       },
--       witness_2 := begin tidy, rw is_Isomorphism_in_Types.witness_2 f.map w, end -- FIXME why doesn't this work without the explicit arguments (or even just by simp)
--     }
--   },
--   preserves_limits := RepresentableFunctorPreservesLimits ForgetfulFunctor_Monoids_to_Types,
-- }


end categories.examples.rings
