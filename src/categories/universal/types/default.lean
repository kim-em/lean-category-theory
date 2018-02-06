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
    factorisation := ♯,
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
    factorisation := ♯,
    uniqueness    := begin
                       tidy,
                       have p := witness x_fst,
                       tidy
                     end
  }
}
attribute [instance] Types_has_Coproducts

-- PROJECT better automation.
definition {u} Types_has_Equalizers : has_Equalizers CategoryOfTypes.{u} :=
{ equalizer := λ α _ f g,
  {
    equalizer     := { x : α // f x = g x },
    inclusion     := λ x, x.val,
    witness       := ♯,
    map           := begin
                       tidy,
                       exact k a,
                       tidy,
                    end,
    factorisation := ♯,
    uniqueness    := ♯ 
  }
}
attribute [instance] Types_has_Equalizers

-- Even though this can be automatically generated, this is a much cleaner version.
definition {u} Types_has_BinaryProducts : has_BinaryProducts CategoryOfTypes.{u} := {
  binary_product := λ X Y, {
    product             := X × Y,
    left_projection     := prod.fst,
    right_projection    := prod.snd,
    map                 := λ _ f g z, (f z, g z),
    left_factorisation  := by tidy,
    right_factorisation := by tidy,
    uniqueness          := by tidy
  }
}
attribute [instance] Types_has_BinaryProducts

definition {u} Types_has_BinaryCoproducts : has_BinaryCoproducts CategoryOfTypes.{u} := {
  binary_coproduct := λ X Y, {
    coproduct           := X ⊕ Y,
    left_inclusion     := sum.inl,
    right_inclusion    := sum.inr,
    map                 := λ _ f g z, sum.cases_on z f g,
    left_factorisation  := by tidy,
    right_factorisation := by tidy,
    uniqueness          := begin tidy, induction x, tidy, end
  }
}
attribute [instance] Types_has_BinaryCoproducts

-- Does Types have coequalizers? Quotients are hard.
-- definition {u} relation_from_functions { α β : Type u } ( f g : α → β ) : β → β → Prop :=
--   λ b0 bn : β, ∃ l : list α, 

end categories.types