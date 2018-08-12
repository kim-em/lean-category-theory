-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.equivalence
import categories.types

namespace category_theory

universes u

class concrete (C : Type (u+1)) [large_category C] := 
  (fibre_functor : C ↝ (Type u))
  (faithfulness : faithful fibre_functor . obviously)

def fibre_functor (C : Type (u+1)) [large_category C] [concrete : concrete C] := concrete.fibre_functor

instance : concrete (Type u) := 
{ fibre_functor := functor.id _ }

end category_theory