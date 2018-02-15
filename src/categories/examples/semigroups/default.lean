-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ...functor
import ...types

namespace categories.examples.semigroups

universe u

open categories

structure semigroup_morphism {α β : Type u} (s : semigroup α) (t: semigroup β) : Type (u+1) :=
  (map: α → β)
  (multiplicative : ∀ x y : α, map (semigroup.mul x y) = semigroup.mul (map x) (map y) . obviously)

make_lemma semigroup_morphism.multiplicative
attribute [simp,ematch] semigroup_morphism.multiplicative_lemma

definition monoid_semigroup_to_map {α β : Type u} {s : semigroup α} {t: semigroup β} : has_coe_to_fun (semigroup_morphism s t) :=
{F   := λ f, Π x : α, β,
  coe := semigroup_morphism.map}

attribute [instance] monoid_semigroup_to_map

definition semigroup_identity {α : Type u} (s: semigroup α) : semigroup_morphism s s := ⟨ id ⟩

definition semigroup_morphism_composition
  {α β γ : Type u} {s: semigroup α} {t: semigroup β} {u: semigroup γ}
  (f: semigroup_morphism s t) (g: semigroup_morphism t u) : semigroup_morphism s u :=
{
  map := λ x, g (f x)
}

@[applicable] lemma semigroup_morphism_pointwise_equality
  {α β : Type u} {s : semigroup α} {t: semigroup β}
  (f g : semigroup_morphism s t)
  (w : ∀ x : α, f x = g x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc := funext w,
    subst hc
end

definition Semigroup := Σ α : Type u, semigroup α

instance CategoryOfSemigroups : category Semigroup := {
    Hom := λ s t, semigroup_morphism s.2 t.2,
    identity := λ s, semigroup_identity s.2,
    compose  := λ _ _ _ f g, semigroup_morphism_composition f g
}

definition trivial_semigroup: semigroup punit := {
  mul := λ _ _, punit.star,
  mul_assoc := ♮
}

open categories.functor
open categories.types

definition ForgetfulFunctor_Semigroups_to_Types : Functor Semigroup (Type u) :=
{
  onObjects     := λ s, s.1,
  onMorphisms   := λ s t, λ f, ulift.up f.map,
}

end categories.examples.semigroups
