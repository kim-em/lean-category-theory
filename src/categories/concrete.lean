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
variable {C : Type u}
variable [category C]

-- TODO is this usable?
class Concrete (C : Type (u+1)) [category C] := 
  (F : Functor C (Type u))
  (w : Faithful F . obviously)

instance Types_Concrete : Concrete (Type u) := {
    F := IdentityFunctor (Type u)
}

end categories