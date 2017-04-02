import ..examples.types.types
import .universal

open tqft.categories.universal
open tqft.categories.isomorphism
open tqft.categories.examples.types

definition Equalizer_in_Types { α β : Type } ( f g : α → β ) := @Equalizer CategoryOfTypes _ _ f g

local attribute [pointwise] funext

lemma subtype_is_Equalizer_in_Types { α β : Type } ( f g : α → β ) : Equalizer_in_Types f g :=
{
  equalizer     := { x : α // f x = g x },
  inclusion     := λ x, x.val,
  witness       := begin blast, induction x, blast end,
  factorisation := begin
                     blast, 
                     refine ⟨ _, _ ⟩,
                     begin
                      -- First show that a factorisation exists
                      fapply subtype.mk, 
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

