import ..examples.types.types
import .universal

open tqft.categories.universal
open tqft.categories.isomorphism
open tqft.categories.examples.types

definition {u} Types_has_FiniteCoproducts : has_FiniteCoproducts CategoryOfTypes.{u} :=
{
  initial_object := {
    object := ulift empty,
    morphisms := λ t, λ x, match x with end,
    uniqueness := begin intros, apply funext, intros, induction x, induction down end
  },
  binary_coproduct := λ X Y,
  {
    coproduct := sum X Y,
    left_inclusion := λ x, sum.inl x,
    right_inclusion := λ y, sum.inr y,
    map := λ Z f g, λ z, match z with | sum.inl x := f x | sum.inr y := g y end,
    left_factorisation := ♯,
    right_factorisation := ♯,
    uniqueness := begin
                    blast,                    
                    induction x,
                    exact congr_fun left_witness a,
                    exact congr_fun right_witness a,
                  end
    }
  }

attribute [instance] Types_has_FiniteCoproducts

definition {u} Types_has_FiniteProducts : has_FiniteProducts CategoryOfTypes.{u} :=
{
  terminal_object := {
    object := punit,
    morphisms := λ t, λ x, punit.star,
    uniqueness := begin intros, apply funext, intros, blast end
  },
  binary_product := λ X Y, {
    product := X × Y,
    left_projection  := λ p, p.1,
    right_projection := λ p, p.2,
    map := λ Z, λ f g, λ z, (f z, g z),
    left_factorisation := ♯,
    right_factorisation := ♯,
    uniqueness := begin
                    blast, 
                    exact congr_fun left_witness x,
                    exact congr_fun right_witness x,              
                  end
  }
}
attribute [instance] Types_has_FiniteProducts

-- PROJECT better automation.
definition {u} Types_has_Equalizers : has_Equalizers CategoryOfTypes.{u} :=
{ equalizer := λ α _ f g,
  {
    equalizer     := { x : α // f x = g x },
    inclusion     := λ x, x.val,
    witness       := begin blast, exact x.property end,
    map           := begin blast, intros, fsplit, exact k a, exact congr_fun w a end,
    factorisation := ♯,
    uniqueness    := begin blast, exact congr_fun witness x end
  }
}
attribute [instance] Types_has_Equalizers

-- Types doesn't have coequalizers; quotients are hard.
