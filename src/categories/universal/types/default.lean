import ...types
import ..instances

open categories.universal
open categories.isomorphism
namespace categories.types

definition {u} Types_has_Products : has_Products.{u+1 u u} CategoryOfTypes.{u} := {
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
attribute [instance] Types_has_Products

definition {u} Types_has_Coproducts : has_Coproducts.{u+1 u u} CategoryOfTypes.{u} := {
  coproduct := λ I φ, {
    coproduct     := Σ i : I, φ i,
    inclusion     := λ i x, ⟨ i, x ⟩ ,
    map           := λ Z f p, f p.1 p.2, 
    uniqueness    := begin
                       tidy,
                       have p := witness x_fst,
                       tidy
                     end
 }
}
attribute [instance] Types_has_Coproducts


definition {u} Types_has_Equalizers : has_Equalizers CategoryOfTypes.{u} := {
  equalizer := λ α _ f g, {
    equalizer     := {x : α // f x = g x},
    inclusion     := λ x, x.val,
    map           := ♯
 }
}
attribute [instance] Types_has_Equalizers

-- Even though this can be automatically generated, this is a much cleaner version.
definition {u} Types_has_BinaryProducts : has_BinaryProducts CategoryOfTypes.{u} := {
  binary_product := λ X Y, {
    product             := X × Y,
    left_projection     := prod.fst,
    right_projection    := prod.snd,
    map                 := λ _ f g z, (f z, g z)
 }
}
attribute [instance] Types_has_BinaryProducts

definition {u} Types_has_BinaryCoproducts : has_BinaryCoproducts CategoryOfTypes.{u} := {
  binary_coproduct := λ X Y, {
    coproduct           := X ⊕ Y,
    left_inclusion     := sum.inl,
    right_inclusion    := sum.inr,
    map                 := λ _ f g z, sum.cases_on z f g,
    uniqueness          := begin tidy, induction x, tidy, end
 }
}
attribute [instance] Types_has_BinaryCoproducts

-- TODO ask if this can live in mathlib? I've also needed it for Mitchell's group theory work.
@[simp] lemma {u₁ u₂} parallel_transport_for_trivial_bundles {α : Sort u₁} {a b : α} {β : Sort u₂} (p : a = b) (x : β) : @eq.rec α a (λ a, β) x b p = x :=
begin
induction p,
simp,
end

definition {u} Types_has_Coequalizers : has_Coequalizers CategoryOfTypes.{u} :=
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
attribute [instance] Types_has_Equalizers


end categories.types