-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .universal
import .comparisons

open tqft.categories
open tqft.categories.universal

namespace tqft.categories.universal

lemma Equalizers_are_unique
  { C : Category }  
  { X Y : C.Obj } 
  ( f g : C.Hom X Y )
   : unique_up_to_isomorphism (Equalizer f g) Equalizer.equalizer
   := sorry -- PROJECT prove this via the comma category formulation, using lemmas in comparisons.lean

end tqft.categories.universal

