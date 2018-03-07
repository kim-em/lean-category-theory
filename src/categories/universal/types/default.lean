import ...types
import ..instances
import ...transport

open categories.universal
open categories.isomorphism
namespace categories.types

universe u

instance Types_has_Products : has_Products (Type u) := {
  product := λ I φ, {
    product       := Π i : I, φ i,
    projection    := λ i x, x i,
    map           := λ Z f z i, f i z, 
    uniqueness    := begin
                       tidy,
                       have p := witness x_1,
                       tidy,
                     end
 }
}

instance Types_has_Coproducts : has_Coproducts (Type u) := {
  coproduct := λ I φ, {
    coproduct     := Σ i : I, φ i,
    inclusion     := λ i x, ⟨ i, x ⟩,
    map           := λ Z f p, f p.1 p.2, 
    uniqueness    := begin
                       tidy,
                       have p := witness x_fst,
                       tidy
                     end
 }
}

instance Types_has_Equalizers : has_Equalizers (Type u)  := {
  equalizer := λ α β f g, {
    equalizer     := {x : α // f x = g x},
    inclusion     := λ x, x.val,
    map           := λ γ k h g, ⟨ k g, ♯ ⟩
 }
}

-- Even though this can be automatically generated, this is a much cleaner version.
instance Types_has_BinaryProducts : has_BinaryProducts (Type u)  := {
  binary_product := λ X Y, {
    product             := X × Y,
    left_projection     := prod.fst,
    right_projection    := prod.snd,
    map                 := λ _ f g z, (f z, g z)
 }
}

instance Types_has_BinaryCoproducts : has_BinaryCoproducts (Type u)  := {
  binary_coproduct := λ X Y, {
    coproduct           := X ⊕ Y,
    left_inclusion     := sum.inl,
    right_inclusion    := sum.inr,
    map                 := λ _ f g z, sum.cases_on z f g,
    uniqueness          := λ Z f g lw rw, begin tidy, induction x, tidy, end
 }
}


instance Types_has_Coequalizers : has_Coequalizers (Type u)  :=
{coequalizer := λ α β f g,
  {
    coequalizer   := quotient (eqv_gen.setoid (λ x y, ∃ a : α, f a = x ∧ g a = y)),
    projection    := λ x, begin apply quotient.mk, exact x end,
    witness       := begin tidy, apply quotient.sound, apply eqv_gen.rel, existsi x, simp, end,
    map           := begin
                       tidy, 
                       induction a, 
                       exact k a, 
                       induction a_p, 
                       tidy,  -- TODO I'm confused why this can't be changed to obviously
                       rw a_p_ih_a, 
                       rw a_p_ih_a_1,
                     end,
    factorisation := ♯,
    uniqueness    := begin
                       tidy,
                       induction x,
                       have p := congr_fun witness x,
                       tidy,
                     end 
 }
}


end categories.types