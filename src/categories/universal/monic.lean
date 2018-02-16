-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .universal
import ..monic

open categories
open categories.universal
open categories.isomorphism

namespace categories

universe u
variable {C : Type u}
variable [category C]
variables {X Y Z : C}

structure RegularMonic (f : Hom X Y) :=
  (Z : C)
  (a b : Hom Y Z)
  (e : Equalizer a b)
  (i : Isomorphism e.equalizer X)
  (w : e.inclusion = i.morphism ≫ f)

-- EXERCISE
-- lemma SplitMonic_implies_RegularMonic
--   {f : Hom X Y} 
--   (s : SplitMonic f) : RegularMonic f := sorry

-- EXERCISE
-- lemma RegularMonic_implies_Monic
--   {f : Hom X Y} 
--   (s : RegularMonic f) : Monic f := sorry

structure RegularEpic (f : Hom Y Z) :=
  (X : C)
  (a b : Hom X Y)
  (c : Coequalizer a b)
  (i : Isomorphism c.coequalizer Z)
  (w : c.projection = f ≫ i.inverse)

end categories