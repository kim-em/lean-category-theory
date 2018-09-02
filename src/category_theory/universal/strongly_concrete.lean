-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.continuous
import category_theory.concrete
import category_theory.functor.isomorphism

open category_theory

namespace category_theory.universal

universes u
variable (C : Type (u+1))
variable [large_category C]

class strongly_concrete [concrete C] :=
(reflects_isos    : reflects_isos (concrete.fibre_functor C))
(preserves_limits : continuous (concrete.fibre_functor C))

-- PROJECT
instance type_strongly_concrete : strongly_concrete (Type u) := {
    reflects_isos := sorry,
    preserves_limits := sorry
}

end category_theory.universal