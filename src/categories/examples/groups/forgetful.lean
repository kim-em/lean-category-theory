import ..groups
import ...types
import ...yoneda
import algebra.group_power

namespace categories.examples.groups
open categories.functor
open categories.types
open categories.yoneda

universes u₁ u₂

definition ForgetfulFunctor_Groups_to_Types : Functor.{(u₁+1) (u₁+2)} Group (Type (u₁+1)) :=
{
  onObjects     := λ s, ulift.{u₁+1} s.1,
  onMorphisms   := λ s t, λ f, ulift.up (λ x, ulift.up (f.map x.down)),
}

-- -- yuck
-- @[simp] private lemma monoid_pow_add {α} [monoid α] (a : α) (x y : ℕ) : monoid.pow a (nat.add x y) = monoid.mul (monoid.pow a x) (monoid.pow a y) :=
-- begin
-- have p : (nat.add x y) = x + y, by unfold has_add.add,
-- rw p,
-- rw pow_add,
-- refl,
-- end

-- -- yuck
-- @[simp] private lemma monoid_pow_nat {α} [m : monoid α] (f : monoid_morphism ℕ_as_monoid_under_addition m) (n : ℕ): monoid.pow (f.map 1) n = f.map n :=
-- begin
-- induction n,
-- {tidy, erw f.unital_lemma,},
-- {
--   unfold monoid.pow,
--   have p : nat.succ n_n = 1 + n_n, by simp,
--   rw p,
--   erw f.multiplicative_lemma,
--   rw n_ih,
--   refl,
-- }
-- end

instance ulift_group {α : Type u₁} [group α] : group (ulift.{u₂} α) := 
begin
refine {
    one := ulift.up 1,
    mul := λ x y, ulift.up (x.down * y.down),
    inv := λ x, ulift.up ((x.down)⁻¹),
    ..
},
all_goals { sorry }
end

instance integers_as_group : group ℤ := 
begin
  refine {
    one := 0,
    mul := λ x y, x + y,
    inv := λ x, -x,
    ..
  } ; intros ; simp
end

#eval groups.integers_as_group.one

-- TODO fix inconsistent naming of monoid.pow and gpow in mathlib
local attribute [class] is_group_hom
instance exponentiation_is_hom (G : Group) (g : G.1) : is_group_hom (λ (n : ulift ℤ), gpow g (n.down)) := sorry
@[simp] lemma hom_exponentiation (G : Group) (f : ulift ℤ → G.1) [is_group_hom f] (n : ℤ) : gpow (f (ulift.up int.one)) n = f (ulift.up n) := sorry

-- set_option trace.class_instances true
instance Groups_ForgetfulFunctor_Representable : @Representable.{u₁+1} Group _ (ForgetfulFunctor_Groups_to_Types.{u₁}) := {
  c := ⟨ ulift ℤ, by apply_instance ⟩,
  Φ := {
    morphism := {
      components := λ G, ulift.up (λ g, ⟨λ n, gpow g.down n.down, begin tidy, apply_instance end⟩),
      naturality := sorry
   },
    inverse := {
      components := λ G, ulift.up (λ f, ulift.up (f.map (ulift.up (1 : ℤ))))
   }
 }
}

end categories.examples.groups