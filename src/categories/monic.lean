-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories

structure Monic {C : Category} {Y Z : C.Obj} (f : C.Hom Y Z) :=
  (witness : ∀ {X : C.Obj} {a b : C.Hom X Y} (p : C.compose a f = C.compose b f), a = b)
structure Epic {C : Category} {X Y : C.Obj} (f : C.Hom X Y) :=
  (witness : ∀ {Z : C.Obj} {a b : C.Hom Y Z} (p : C.compose f a = C.compose f b), a = b)

structure SplitMonic {C : Category} {Y Z : C.Obj} (f : C.Hom Y Z) :=
  (right_inverse : C.Hom Z Y)
  (evidence      : C.compose f right_inverse = C.identity Y)

lemma SplitMonic_implies_Monic {C : Category} {Y Z : C.Obj} {f : C.Hom Y Z} (m : SplitMonic f) : Monic f := {
    witness := λ _ a b p, begin
                            have e := congr_arg (λ g, C.compose g m.right_inverse) p,
                            simp at e,
                            -- repeat_at_least_once {rewrite C.associativity at e},
                            repeat_at_least_once {rewrite m.evidence at e},
                            simp at e,
                            exact e
                          end
} 

end categories