-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .equivalence
import .types

namespace categories

open categories.types
open categories.functor
open categories.equivalence

universe u

-- TODO is this usable?
class Concrete (C : Type (u+1)) [category C] := 
  (fibre_functor : C ↝ (Type u))
  (faithfulness : Faithful fibre_functor . obviously)

definition FibreFunctor (C : Type (u+1)) [category C] [concrete : Concrete C] := concrete.fibre_functor

instance Types_Concrete : Concrete (Type u) := {
    fibre_functor := 1
}

end categories