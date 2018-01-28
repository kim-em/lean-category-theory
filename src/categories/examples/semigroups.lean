-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import categories.functor
import categories.types
import categories.universal.instances

namespace categories.examples.semigroups

open categories

structure {u} semigroup_morphism { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) :=
  (map: α → β)
  (multiplicative : ∀ x y : α, map (semigroup.mul x y) = semigroup.mul (map x) (map y) . tidy')

make_lemma semigroup_morphism.multiplicative
attribute [ematch] semigroup_morphism.multiplicative_lemma

definition {u} monoid_semigroup_to_map { α β : Type u } { s : semigroup α } { t: semigroup β } : has_coe_to_fun (semigroup_morphism s t) :=
{ F   := λ f, Π x : α, β,
  coe := semigroup_morphism.map }

attribute [instance] monoid_semigroup_to_map

definition {u} semigroup_identity { α : Type u } ( s: semigroup α ) : semigroup_morphism s s := ⟨ id ⟩

definition {u} semigroup_morphism_composition
  { α β γ : Type u } { s: semigroup α } { t: semigroup β } { u: semigroup γ}
  ( f: semigroup_morphism s t ) ( g: semigroup_morphism t u ) : semigroup_morphism s u :=
{
  map := λ x, g (f x)
}

@[applicable] lemma {u} semigroup_morphism_pointwise_equality
  { α β : Type u } { s : semigroup α } { t: semigroup β }
  ( f g : semigroup_morphism s t )
  ( w : ∀ x : α, f x = g x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc := funext w,
    subst hc
end

definition {u} CategoryOfSemigroups : Category := 
{
    Obj := Σ α : Type u, semigroup α,
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
open categories.initial

definition ForgetfulFunctor_Semigroups_to_Types : Functor CategoryOfSemigroups CategoryOfTypes :=
{
  onObjects     := λ s, s.1,
  onMorphisms   := λ s t, λ f, f.map,
}

open categories.universal

@[applicable] lemma {u} punit_equality
  ( a b : punit.{u} ): a = b := ♯

instance Semigroups_has_TerminalObject : has_TerminalObject CategoryOfSemigroups := {
  terminal_object := {
    terminal_object := ⟨ punit, trivial_semigroup ⟩,
    morphism_to_terminal_object_from := ♯
  }
}

-- instance Semigroups_has_BinaryProducts : has_BinaryProducts CategoryOfSemigroups := {
--   binary_product := λ s t, {
--     product             := ⟨ s.1 × t.1, semigroup_product s.2 t.2 ⟩ ,
--     left_projection     := {
--       map := prod.fst,
--       multiplicative := ♯
--     },
--     right_projection    := {
--       map := prod.snd,
--       multiplicative := ♯
--     },
--     map                 := λ r f g, {
--       map := λ x, (f.map x, g.map x),
--       multiplicative := ♯ 
--     },
--     left_factorisation  := ♯,
--     right_factorisation := ♯,
--     uniqueness          := λ r f g w₁ w₂, begin
--       apply semigroup_morphism_pointwise_equality,
--       intro x,
--       apply pairs_componentwise_equal,
--       admit,
--       admit
--     end
--   }
-- }

end categories.examples.semigroups
