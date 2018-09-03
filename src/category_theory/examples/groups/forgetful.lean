-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.examples.groups
import category_theory.types
import category_theory.representable
import algebra.group_power

namespace category_theory.examples.groups

open category_theory
open category_theory.yoneda

universes u₁ u₂

def ForgetfulFunctor_Groups_to_Types : Group ⥤ (Type u₁) :=
{ obj  := λ s, s.1,
  map' := λ s t f x, f.map x }

local attribute [search] semigroup.mul_assoc

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

instance exponentiation_is_hom (G : Group) (g : G.1) : is_group_hom (λ (n : ℤ), gpow g n) := begin tidy, sorry end
instance exponentiation_is_hom' (G : Group) (g : G.1) : is_group_hom (λ (n : _root_.ulift ℤ), gpow g (n.down)) := begin tidy, sorry end
@[simp] lemma hom_exponentiation (G : Group) (f : _root_.ulift ℤ → G.1) [is_group_hom f] (n : ℤ) : gpow (f (ulift.up int.one)) n = f (ulift.up n) := sorry

@[simp] lemma monoid_pow_one {G} [group G] (x : G) : monoid.pow x 1 = x := begin sorry, end

instance Groups_ForgetfulFunctor_Representable : representable (ForgetfulFunctor_Groups_to_Types.{u₁}) := 
{ c := ⟨ _root_.ulift ℤ, by apply_instance ⟩,
  Φ := { hom := { app := λ G g, ⟨λ n, gpow g n.down, begin tidy, sorry end⟩,
                        naturality' := sorry },
          inv := { app := λ G f, f.map (ulift.up (1 : ℤ)), },
          hom_inv_id' := sorry,
          inv_hom_id' := sorry, } }

end category_theory.examples.groups