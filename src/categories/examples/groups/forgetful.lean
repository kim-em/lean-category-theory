-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.examples.groups
import categories.types
import categories.yoneda
import algebra.group_power

namespace categories.examples.groups
open categories
open categories.functor
open categories.types
open categories.yoneda

universes u₁ u₂

definition ForgetfulFunctor_Groups_to_Types : Group ↝ (Type u₁) :=
{ onObjects     := λ s, s.1,
  onMorphisms   := λ s t f x, f.map x, }

local attribute [ematch] semigroup.mul_assoc

instance ulift_group {α : Type u₁} [group α] : group (ulift.{u₂} α) := 
begin
refine { one := ulift.up 1,
         mul := λ x y, ulift.up (x.down * y.down),
         inv := λ x, ulift.up ((x.down)⁻¹),
         .. } ; obviously
end

instance integers_as_group : group ℤ := 
begin
  refine {
    one := 0,
    mul := λ x y, x + y,
    inv := λ x, -x,
    ..
  } ; obviously
end

-- TODO fix inconsistent naming of monoid.pow and gpow in mathlib
local attribute [class] is_group_hom

instance exponentiation_is_hom (G : Group) (g : G.1) : is_group_hom (λ (n : ℤ), gpow g n) := λ a b, begin intros, funext, dsimp, /- rewrite gpow_add, -/ sorry end
instance exponentiation_is_hom' (G : Group) (g : G.1) : is_group_hom (λ (n : ulift ℤ), gpow g (n.down)) := λ a b, begin intros, funext, cases a, cases b, dsimp, sorry end
@[simp] lemma hom_exponentiation (G : Group) (f : ulift ℤ → G.1) [is_group_hom f] (n : ℤ) : gpow (f (ulift.up int.one)) n = f (ulift.up n) := sorry

@[simp] lemma monoid_pow_one {G} [group G] (x : G) : monoid.pow x 1 = x := begin sorry, end

instance Groups_ForgetfulFunctor_Representable : @Representable.{u₁} Group _ (ForgetfulFunctor_Groups_to_Types.{u₁}) := {
  c := ⟨ ulift ℤ, by apply_instance ⟩,
  Φ := {
    morphism := {
      components := λ G g, ⟨λ n, gpow g n.down, begin tidy, apply_instance end⟩,
      naturality := sorry
   },
    inverse := {
      components := λ G f, f.map (ulift.up (1 : ℤ)),
   },
   witness_2 := sorry,
 }
}

end categories.examples.groups