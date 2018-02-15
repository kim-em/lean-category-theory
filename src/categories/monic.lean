-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories

universe u
variable {C : Type u}
variable [category C]
variables {X Y Z : C}

structure Monic (f : Hom Y Z) :=
  (witness : ∀ {X : C} {a b : Hom X Y} (p : a >> f = b >> f), a = b)
structure Epic (f : Hom X Y) :=
  (witness : ∀ {Z : C} {a b : Hom Y Z} (p : f >> a = f >> b), a = b)

structure SplitMonic (f : Hom Y Z) :=
  (right_inverse : Hom Z Y)
  (evidence      : f >> right_inverse = 𝟙 Y)

lemma SplitMonic_implies_Monic {f : Hom Y Z} (m : SplitMonic f) : Monic f := {
    witness := λ _ a b p, begin
                            have e := congr_arg (λ g, g >> m.right_inverse) p,
                            simp at e,
                            -- repeat_at_least_once {rewrite C.associativity at e},
                            repeat_at_least_once {rewrite m.evidence at e},
                            simp at e,
                            exact e
                          end
} 

end categories