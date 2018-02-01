-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.functor
import .semigroups
import ..universal.strongly_concrete
import algebra.group_power
import tactic.ring

namespace categories.examples.monoids

open categories

structure monoid_morphism { α β : Type } ( s : monoid α ) ( t : monoid β ) :=
  ( map: α → β )
  ( multiplicative : ∀ x y : α, map (monoid.mul x y) = monoid.mul (map x) (map y) . tidy' )
  ( unital : map(s.one) = t.one . tidy' )

make_lemma monoid_morphism.multiplicative
make_lemma monoid_morphism.unital
attribute [simp] monoid_morphism.multiplicative_lemma monoid_morphism.unital_lemma

@[simp] lemma monoid_morphism_power { α β : Type } { s : monoid α } { t : monoid β } ( f : monoid_morphism s t ) ( a : α ) ( n : ℕ ) : f.map (@monoid.pow α s a n) = @monoid.pow β t (f.map a) n :=
begin
induction n,
{ tidy },
{ unfold monoid.pow, tidy }
end

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

open categories.types

definition ForgetfulFunctor_Monoids_to_Types : Functor CategoryOfMonoids CategoryOfTypes :=
{
    onObjects   := λ r, r.1,
    onMorphisms := λ _ _ f, f.map 
  }

definition Monoids_Concrete : Concrete CategoryOfMonoids := {
  F := ForgetfulFunctor_Monoids_to_Types
}
attribute [instance] Monoids_Concrete

open categories.yoneda

local attribute [tidy] ring

definition ℕ_as_monoid_under_addition : monoid ℕ := {
  one := 0,
  mul := λ x y : ℕ , x + y,
  one_mul := begin intros, simp [has_mul.mul] end,
  mul_one := begin intros, simp [has_mul.mul] end,
  mul_assoc := begin intros, simp [has_mul.mul] end
}
attribute [instance] ℕ_as_monoid_under_addition

-- yuck
@[simp] private lemma monoid_pow_add {α} [monoid α] (a : α) (x y : ℕ) : monoid.pow a (nat.add x y) = monoid.mul (monoid.pow a x) (monoid.pow a y) :=
begin
have p : (nat.add x y) = x + y, by unfold has_add.add,
rw p,
rw pow_add,
refl,
end

-- yuck
@[simp] private lemma monoid_pow_nat {α} [m : monoid α] (f : monoid_morphism ℕ_as_monoid_under_addition m) (n : ℕ): monoid.pow (f.map 1) n = f.map n :=
begin
induction n,
{ tidy, erw f.unital_lemma, },
{
  unfold monoid.pow,
  have p : nat.succ n_n = 1 + n_n, by simp,
  rw p,
  erw f.multiplicative_lemma,
  rw n_ih,
  refl,
}
end


instance Monoids_ForgetfulFunctor_Representable : Representable (ForgetfulFunctor_Monoids_to_Types) := {
  c := ⟨ ℕ, ℕ_as_monoid_under_addition ⟩,
  Φ := {
    morphism := {
      components := λ r a, {
        map := λ n, @monoid.pow r.1 r.2 a n,
      },
    },
    inverse := {
      components := λ r f, f.map 1
    }
  }
}

open categories.universal

instance Monoids_StronglyConcrete : StronglyConcrete CategoryOfMonoids := {
  F := ForgetfulFunctor_Monoids_to_Types,
  reflects_isos := {
    reflects := λ X Y f w, {
      inverse := {
        map := w.inverse,
        multiplicative := sorry,
        unital := sorry
      },
      witness_2 := begin tidy, rw is_Isomorphism_in_Types.witness_2 f.map w, end -- FIXME why doesn't this work without the explicit arguments (or even just by simp)
    }
  },
  preserves_limits := RepresentableFunctorPreservesLimits ForgetfulFunctor_Monoids_to_Types,
}


end categories.examples.monoids
