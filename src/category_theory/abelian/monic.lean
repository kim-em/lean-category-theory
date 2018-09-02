-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.isomorphism
import category_theory.tactics.obviously

namespace category_theory

universe u
variable {C : Type (u+1)}
variable [large_category C]
variables {X Y Z : C}

structure split_mono (f : Y ⟶ Z) :=
(right_inverse : Z ⟶ Y)
(evidence'      : f ≫ right_inverse = 𝟙 Y . obviously)

restate_axiom split_mono.evidence'
attribute [simp,ematch] split_mono.evidence

def mono.of_split_mono {f : Y ⟶ Z} (m : split_mono f) : mono f := 
{ right_cancellation := λ _ a b p, begin
                            have e := congr_arg (λ g, g ≫ m.right_inverse) p,
                            obviously,                            
                          end } 

-- PROJECT split_epi

end category_theory