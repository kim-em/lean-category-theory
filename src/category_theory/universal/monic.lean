-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal
import category_theory.abelian.monic

open category_theory
open category_theory.universal

namespace category_theory.universal.monic

universe u
variable {C : Type (u+1)}
variable [large_category C]
variables {X Y Z : C}

structure RegularMonic (f : X ⟶ Y) :=
(Z : C)
(a b : Y ⟶ Z)
(e : Equalizer a b)
(i : e.equalizer ≅ X)
(w : e.inclusion = i.hom ≫ f)

-- EXERCISE
-- def SplitMonic_implies_RegularMonic
--   {f : Hom X Y} 
--   (s : SplitMonic f) : RegularMonic f := sorry

-- EXERCISE
-- def RegularMonic_implies_Monic
--   {f : Hom X Y} 
--   (s : RegularMonic f) : Monic f := sorry

structure RegularEpic (f : Y ⟶ Z) :=
(X : C)
(a b : X ⟶ Y)
(c : Coequalizer a b)
(i : c.coequalizer ≅ Z)
(w : c.projection = f ≫ i.inv)

end category_theory.universal.monic