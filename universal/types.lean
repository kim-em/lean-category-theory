import ..examples.types.types
import .universal

open tqft.categories.universal
open tqft.categories.isomorphism
open tqft.categories.examples.types

definition Equalizer_in_Types { α β : Type } ( f g : α → β ) := @Equalizer CategoryOfTypes _ _ f g

local attribute [pointwise] funext

lemma subtype_is_ExplicitEqualizer_in_Types { α β : Type } ( f g : α → β ) : Equalizer_in_Types f g :=
{
  equalizer     := { x : α // f x = g x },
  inclusion     := λ x, x.val,
  witness       := begin blast, induction x, blast end,
  factorisation := begin
                     blast, 
                     fapply subtype.mk, 
                     intros, 
                     unfold CategoryOfTypes at k, 
                     dsimp at k, 
                     refine ⟨ k a, _ ⟩, 
                     intros, 
                     unfold CategoryOfTypes at w, 
                     dsimp at w, 
                     exact congr_arg (λ x: Z → β, x a) w, 
                     blast
                   end
}

lemma ExplicitEqualizer_in_Types_is_subtype { α β : Type } ( f g : α → β ) ( equalizer : Equalizer_in_Types f g )
  : @Isomorphism CategoryOfTypes equalizer^.equalizer { x : α // f x = g x } :=
{
  morphism := sorry,  
  inverse  := sorry,
  witness_1 := sorry,
  witness_2 := sorry
}
