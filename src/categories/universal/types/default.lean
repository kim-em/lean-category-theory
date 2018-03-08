import ...types
import ..instances
import ...transport
import tactic.finish
open categories.universal
open categories.isomorphism
namespace categories.types

universe u

@[simp] lemma funext_simp {α β} {f g : α → β} : (f = g) = ∀ a : α, f a = g a :=
begin
apply propext,
split,
{ intro w, intro, rw w },
{ intro w, apply funext, assumption }
end 
instance Types_has_Products : has_Products (Type u) := {
  product := λ I φ, {
    product       := Π i : I, φ i,
    projection    := λ i x, x i,
    map           := λ Z f z i, f i z, 
 }
}

instance Types_has_Coproducts : has_Coproducts (Type u) := {
  coproduct := λ I φ, {
    coproduct     := Σ i : I, φ i,
    inclusion     := λ i x, ⟨ i, x ⟩,
    map           := λ Z f p, f p.1 p.2, 
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
    uniqueness          := λ Z f g lw rw, begin tidy, induction x, obviously, obviously, end
 }
}


instance Types_has_Coequalizers : has_Coequalizers (Type u)  :=
{coequalizer := λ α β f g,
  {
    coequalizer   := quotient (eqv_gen.setoid (λ x y, ∃ a : α, f a = x ∧ g a = y)),
    projection    := λ x, begin apply quotient.mk, exact x end, -- FIXME rip out auto_cast, and just write ⟦ x ⟧ here
    witness       := begin tidy, apply quotient.sound, apply eqv_gen.rel, existsi x, simp, end,
    map           := begin
                       tidy, 
                       induction a, 
                       exact k a, 
                       induction a_p, 
                       tidy,
                       obviously, -- FIXME you shouldn't have to call obviously twice
                       obviously, 
                     end,
    factorisation := ♯,
    uniqueness    := begin
                       tidy,
                       induction x,
                       erw witness x, -- TODO is erw necessary here? why?
                       obviously,
                       apply proof_irrel, -- FIXME make proof_irrel applicable.
                     end 
 }
}


end categories.types