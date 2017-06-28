import ..types
import .universal

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
                       have q := congr_fun p x,
                       dsimp at q,
                       exact q
                     end
  }
}

definition {u} Types_has_Coproducts : has_Coproducts CategoryOfTypes.{u} := {
  coproduct := λ I φ, {
    coproduct     := Σ i : I, φ i,
    inclusion     := λ i x, ⟨ i, x ⟩ ,
    map           := λ Z f p, f p.1 p.2, 
    factorisation := ♯,
    uniqueness    := begin
                       tidy,
                       have p := witness fst,
                       have q := congr_fun p snd,
                       dsimp at q,
                       exact q
                     end
  }
}


-- PROJECT better automation.
definition {u} Types_has_Equalizers : has_Equalizers CategoryOfTypes.{u} :=
{ equalizer := λ α _ f g,
  {
    equalizer     := { x : α // f x = g x },
    inclusion     := λ x, x.val,
    witness       := ♯,
    map           := begin
                       tidy,
                       {
                         exact k a
                       },
                       {
                         tidy,
                         have p := congr_fun w a, -- FIXME weird that I can use `have` then `exact`, but can't just use `exact` in one step.
                         exact p
                       }
                    end,
    factorisation := ♯,
    uniqueness    := begin blast, exact congr_fun witness x end
  }
}
attribute [instance] Types_has_Equalizers

-- Types doesn't have coequalizers; quotients are hard.
end categories.types