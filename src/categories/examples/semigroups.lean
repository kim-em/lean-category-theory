-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import categories.functor
import categories.types
import categories.universal.instances
import tidy.its

namespace categories.examples.semigroups

open categories

structure {u} semigroup_morphism { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) :=
  (map: α → β)
  (multiplicative : ∀ x y : α, map (semigroup.mul x y) = semigroup.mul (map x) (map y) . tidy')

make_lemma semigroup_morphism.multiplicative
attribute [simp,ematch] semigroup_morphism.multiplicative_lemma

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

local attribute [applicable] semigroup.mul_assoc

definition {u} semigroup_binary_product { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) : semigroup (α × β) := {
  mul := λ p q, (p.fst * q.fst, p.snd * q.snd),
  mul_assoc := ♯
}

definition {u} semigroup_morphism_binary_product
  { α β γ δ : Type u }
  { s_f : semigroup α } { s_g: semigroup β } { t_f : semigroup γ } { t_g: semigroup δ }
  ( f : semigroup_morphism s_f t_f ) ( g : semigroup_morphism s_g t_g )
  : semigroup_morphism (semigroup_binary_product s_f s_g) (semigroup_binary_product t_f t_g) := {
  map := λ p, (f p.1, g p.2)
}

instance Semigroups_has_BinaryProducts : has_BinaryProducts CategoryOfSemigroups := {
  binary_product := λ s t, {
    product             := ⟨ _, semigroup_binary_product s.2 t.2 ⟩ ,
    left_projection     := ⟨ prod.fst ⟩,
    right_projection    := ⟨ prod.snd ⟩,
    map                 := λ _ f g, {
      map := λ x, (f.map x, g.map x)
    },
    uniqueness          := λ _ f g w₁ w₂, begin
                                             tidy,
                                             have p := congr_arg semigroup_morphism.map w₁,
                                             have p' := congr_fun p x,
                                             exact p',
                                             have q := congr_arg semigroup_morphism.map w₂,
                                             have q' := congr_fun q x,
                                             exact q',
                                          end
  }
}

definition {u v} semigroup_product { I : Type u } { f : I → Type v } ( s : Π i : I, semigroup (f i) ) : semigroup (Π i, f i) := {
  mul := λ p q i, (p i) * (q i),
  mul_assoc := ♯
}

definition {u v} semigroup_morphism_product
  { I : Type u }
  { f g : I → Type v }
  { s : Π i : I, semigroup (f i) } { t : Π i : I, semigroup (g i) } 
  ( f : Π i : I, semigroup_morphism (s i) (t i) )
  : semigroup_morphism (semigroup_product s) (semigroup_product t) := {
  map := λ p i, (f i) (p i)
}

instance Semigroups_has_Products : has_Products CategoryOfSemigroups := {
  product := λ I F, {
    product    := ⟨ _, semigroup_product (λ i, (F i).2) ⟩,
    projection := λ i, { map := λ f, f i },
    map        := λ _ f, { map := λ y j, (f j).map y },
    uniqueness := λ _ f g w, begin
                               tidy,   
                               have p := congr_arg semigroup_morphism.map (w x_1),
                               have p' := congr_fun p x,
                               exact p',
                             end
  }
}

example : 1+1=2 := by simp

definition {u} semigroup_equalizer { α β : Type u } { r : semigroup α } { s : semigroup β } ( f g : semigroup_morphism r s ) : semigroup { x : α // f.map x = g.map x } := {
  mul := λ p q, ⟨ (p.val) * (q.val), ♯ ⟩ ,
  mul_assoc := ♯
}

instance Semigroups_has_Equalizers : has_Equalizers CategoryOfSemigroups := {
  equalizer := λ X Y f g, {
    equalizer := ⟨ _, semigroup_equalizer f g ⟩,
    inclusion := { map := λ x, x.val },
    map       := λ _ h w, { map := λ x, ⟨ h.map x, begin
                                                    tidy, 
                                                    have p := congr_arg semigroup_morphism.map w,
                                                    have p' := congr_fun p x,
                                                    exact p', 
                                                  end ⟩ },
    uniqueness := λ r h k w, begin 
                               tidy, 
                               have p := congr_arg semigroup_morphism.map w,
                               have p' := congr_fun p x,
                               exact p'
                             end,
  }
}

end categories.examples.semigroups
