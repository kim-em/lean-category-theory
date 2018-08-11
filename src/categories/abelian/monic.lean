-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.category
import categories.tactics.obviously

namespace category_theory

universe u
variable {C : Type (u+1)}
variable [large_category C]
variables {X Y Z : C}

structure Monic (f : Y ⟶ Z) :=
(witness : ∀ {X : C} {a b : X ⟶ Y} (p : a ≫ f = b ≫ f), a = b)
structure Epic (f : X ⟶ Y) :=
(witness : ∀ {Z : C} {a b : Y ⟶ Z} (p : f ≫ a = f ≫ b), a = b)

structure SplitMonic (f : Y ⟶ Z) :=
(right_inverse : Z ⟶ Y)
(evidence      : f ≫ right_inverse = 𝟙 Y . obviously)

restate_axiom SplitMonic.evidence
attribute [simp,ematch] SplitMonic.evidence_lemma

def SplitMonic_implies_Monic {f : Y ⟶ Z} (m : SplitMonic f) : Monic f := 
{ witness := λ _ a b p, begin
                            have e := congr_arg (λ g, g ≫ m.right_inverse) p,
                            obviously,                            
                          end } 

-- PROJECT SplitEpic

end category_theory