-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .equivalence
import .types

namespace categories

open categories.types
open categories.functor
open categories.equivalence

class {u v w} Concrete (C : Category.{u v}) := 
  (F : Functor C CategoryOfTypes.{w})
  (w : Faithful F . tidy')

instance Types_Concrete : Concrete CategoryOfTypes := {
    F := IdentityFunctor CategoryOfTypes
}

end categories