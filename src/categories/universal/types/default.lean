import ...types
import ..instances

open categories.universal
open categories.isomorphism
namespace categories.types

definition {u} Types_has_Products : has_Products CategoryOfTypes.{u} := {
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

definition {u} Types_has_Coproducts : has_Coproducts CategoryOfTypes.{u} := {
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

-- Does Types have coequalizers? Quotients are hard.
-- definition {u} relation_from_functions { α β : Type u } ( f g : α → β ) : β → β → Prop :=
--   λ b0 bn : β, ∃ l : list α, 

end categories.types