-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal
import categories.abelian.monic

open categories
open categories.universal
open categories.isomorphism

namespace categories.universal.monic

universe u
variable {C : Type (u+1)}
variable [category C]
variables {X Y Z : C}

structure RegularMonic (f : X ⟶ Y) :=
  (Z : C)
  (a b : Y ⟶ Z)
  (e : Equalizer a b)
  (i : e.equalizer ≅ X)
  (w : e.inclusion = i.morphism ≫ f)

-- EXERCISE
-- lemma SplitMonic_implies_RegularMonic
--   {f : Hom X Y} 
--   (s : SplitMonic f) : RegularMonic f := sorry

-- EXERCISE
-- lemma RegularMonic_implies_Monic
--   {f : Hom X Y} 
--   (s : RegularMonic f) : Monic f := sorry

structure RegularEpic (f : Y ⟶ Z) :=
  (X : C)
  (a b : X ⟶ Y)
  (c : Coequalizer a b)
  (i : c.coequalizer ≅ Z)
  (w : c.projection = f ≫ i.inverse)

end categories.universal.monic