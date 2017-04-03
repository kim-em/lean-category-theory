import ..examples.types.types
import .universal

open tqft.categories.universal
open tqft.categories.isomorphism
open tqft.categories.examples.types

definition Equalizer_in_Types { α β : Type } ( f g : α → β ) := @Equalizer CategoryOfTypes _ _ f g

local attribute [pointwise] funext
local attribute [ematch] subtype.property

open tactic
meta def fsplit : tactic unit :=
do [c] ← target >>= get_constructors_for | fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= fapply

-- PROJECT better automation.
lemma subtype_is_Equalizer_in_Types { α β : Type } ( f g : α → β ) : Equalizer_in_Types f g :=
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

