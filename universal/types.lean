import ..examples.types.types
import .universal

open tqft.categories.universal
open tqft.categories.isomorphism
open tqft.categories.examples.types

definition {u} Types_has_FiniteProducts : has_FiniteProducts CategoryOfTypes.{u} :=
{
  initial_object := {
    object := ulift empty,
    morphisms := λ t, λ x, match x with end,
    uniqueness := begin intros, apply funext, intros, induction x, induction down end
  },
  binary_product := λ X Y,
  {
    product := X × Y,
    left_projection  := λ p, p.1,
    right_projection := λ p, p.2,
    map := λ Z f g, {
      element := ⟨ λ z, (f z, g z), ♯ ⟩,
      uniqueness := begin
                      blast, 
                      
                      pose p := congr_fun X_1.property.left x, 
                      simp at p, 
                      rewrite - p, 
                      pose q := congr_fun Y_1.property.left x, 
                      simp at q, 
                      rewrite - q,

                      pose p := congr_fun X_1.property.right x, 
                      simp at p, 
                      rewrite - p, 
                      pose q := congr_fun Y_1.property.right x, 
                      simp at q, 
                      rewrite - q                      
                    end
    }
  }
}
attribute [instance] Types_has_FiniteProducts

definition {u} Equalizer_in_Types { α β : Type u } ( f g : α → β ) := @Equalizer CategoryOfTypes _ _ f g

-- PROJECT better automation.
lemma {u} subtype_is_Equalizer_in_Types { α β : Type u } ( f g : α → β ) : Equalizer_in_Types f g :=
{
  equalizer     := { x : α // f x = g x },
  inclusion     := λ x, x.val,
  witness       := ♯,
  factorisation := begin
                     blast,
                     split,
                     begin
                      -- First show that a factorisation exists
                      fsplit, -- PROJECT actually, just use split, and solve for the placeholder!
                      intros, 
                      unfold CategoryOfTypes at k, 
                      dsimp at k, 
                      refine ⟨ k a, _ ⟩,
                      -- we still need to show that it has the factorisation property.
                      intros, 
                      unfold CategoryOfTypes at w, 
                      dsimp at w, 
                      exact congr_arg (λ x: Z → β, x a) w, 
                      blast
                     end,
                     begin                      
                      -- Second, show that the factorisation is unique!
                      blast,
                      pose p := congr_fun X.property x,
                      simp at p,
                      rewrite p,
                      pose q := congr_fun Y.property x,
                      simp at q,
                      rewrite q
                     end
                   end
}

