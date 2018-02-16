import ...types
import ..instances

open categories.universal
open categories.isomorphism
namespace categories.types

universe u

instance Types_has_Products : has_Products (Type u) := {
  product := λ I φ, {
    product       := Π i : I, φ i,
    projection    := λ i, ulift.up (λ x, x i),
    map           := λ Z f, ulift.up (λ z i, (f i).down z), 
    uniqueness    := begin
                       tidy,
                       have p := witness x_1,
                       have p' := congr_arg ulift.down p,
                       tidy,
                     end
 }
}

instance Types_has_Coproducts : has_Coproducts (Type u) := {
  coproduct := λ I φ, {
    coproduct     := Σ i : I, φ i,
    inclusion     := λ i, ulift.up (λ x, ⟨ i, x ⟩),
    map           := λ Z f, ulift.up (λ p, (f p.1).down p.2), 
    uniqueness    := begin
                       tidy,
                       have p := witness x_fst,
                       injection p,
                       tidy
                     end
 }
}

instance Types_has_Equalizers : has_Equalizers (Type u)  := {
  equalizer := λ α β f g, {
    equalizer     := {x : α // f.down x = g.down x},
    inclusion     := ulift.up (λ x, x.val),
    map           := λ γ k h, ulift.up (λ g, ⟨ k.down g, begin tidy, injection h, tidy, end ⟩ )
 }
}

-- Even though this can be automatically generated, this is a much cleaner version.
instance Types_has_BinaryProducts : has_BinaryProducts (Type u)  := {
  binary_product := λ X Y, {
    product             := X × Y,
    left_projection     := prod.1,
    right_projection    := prod.2,
    map                 := λ _ f g z, (f z, g z)
 }
}

instance Types_has_BinaryCoproducts : has_BinaryCoproducts (Type u)  := {
  binary_coproduct := λ X Y, {
    coproduct           := X ⊕ Y,
    left_inclusion     := sum.inl,
    right_inclusion    := sum.inr,
    map                 := λ _ f g z, sum.cases_on z f g,
    uniqueness          := begin tidy, induction x, tidy, end
 }
}

-- TODO ask if this can live in mathlib? I've also needed it for Mitchell's group theory work.
@[simp] lemma {u₁ u₂} parallel_transport_for_trivial_bundles {α : Sort u₁} {a b : α} {β : Sort u₂} (p : a = b) (x : β) : @eq.rec α a (λ a, β) x b p = x :=
begin
induction p,
simp,
end

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
                       tidy, 
                       induction a_p_a, 
                       induction a_p_a_h, 
                       rw ← a_p_a_h_left, 
                       rw ← a_p_a_h_right,
                       exact congr_fun w a_p_a_w,
                       obviously,
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