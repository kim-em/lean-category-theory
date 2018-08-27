import .limits
import .colimits

universe u

namespace category_theory.universal

local attribute [forward] fork.w square.w

instance : has_binary_products.{u+1 u} (Type u) := 
{ prod := λ Y Z, { X := Y × Z, π₁ := prod.fst, π₂ := prod.snd } }

instance : has_products.{u+1 u} (Type u) := 
{ prod := λ β f, { X := Π b, f b, π := λ b x, x b } }.


instance : has_equalizers.{u+1 u} (Type u) := 
{ equalizer := λ Y Z f g, { X := { y : Y // f y = g y }, ι := subtype.val } }

instance : has_pullbacks.{u+1 u} (Type u) := 
{ pullback := λ Y₁ Y₂ Z r₁ r₂, { X := { z : Y₁ × Y₂ // r₁ z.1 = r₂ z.2 }, π₁ := λ z, z.val.1, π₂ := λ z, z.val.2 } }

-- TODO update this stuff on colimits to the newer design:

instance : has_binary_coproducts.{u+1 u} (Type u) := 
{ binary_coproduct := λ Y Z, { X := Y ⊕ Z, ι₁ := sum.inl, ι₂ := sum.inr, h := by obviously } }

-- TODO has_coproducts

local attribute [forward] cofork.w


set_option pp.proofs true
instance : has_coequalizers.{u+1 u} (Type u) := 
{ coequalizer := λ Y Z f g, 
  begin
    letI setoid := eqv_gen.setoid (λ x y, ∃ a : Z, f a = x ∧ g a = y),
    exact { X := quotient setoid, 
            π := by obviously, 
            w := by obviously,
            h := { desc := begin 
                             intros, dsimp,
                             intros, induction a,
                             exact s.π a,
                             induction a_p,
                             obviously,
                             sorry, sorry, sorry -- I'm Canadian.
                           end,
                   fac  := by obviously,
                   uniq := by obviously } }
  end }

end category_theory.universal


