-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.equivalence
import category_theory.types

namespace category_theory

universes u v

class concrete (C : Type u) [category.{u v} C] := 
  (fibre_functor : C ↝ (Type v))
  (faithfulness : faithful fibre_functor . obviously)

instance : concrete (Type u) := 
{ fibre_functor := functor.id _ }

end category_theory