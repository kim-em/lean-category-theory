import ..groups
import ...types
import ...yoneda
import algebra.group_power

namespace categories.examples.groups
open categories.functor
open categories.types
open categories.yoneda

universes u₁ u₂

definition ForgetfulFunctor_Groups_to_Types : Group ↝ (Type u₁) :=
{
  onObjects     := λ s, s.1,
  onMorphisms   := λ s t f x, f.map x,
}

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

@[simp] lemma monoid_pow_one {G} [group G] (x : G) : monoid.pow x 1 = x := begin sorry, end

-- set_option trace.class_instances true
instance Groups_ForgetfulFunctor_Representable : @Representable.{u₁} Group _ (ForgetfulFunctor_Groups_to_Types.{u₁}) := {
  c := ⟨ ulift ℤ, by apply_instance ⟩,
  Φ := {
    morphism := {
      components := λ G g, ⟨λ n, gpow g n.down, begin tidy, apply_instance end⟩,
      naturality := sorry
   },
    inverse := {
      components := λ G f, f.map (ulift.up (1 : ℤ))
   }
 }
}

end categories.examples.groups