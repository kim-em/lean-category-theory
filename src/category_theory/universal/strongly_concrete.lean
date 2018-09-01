-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.continuous
import category_theory.concrete
import category_theory.functor.isomorphism

open category_theory

namespace category_theory.universal

universes u₁
variable (C : Type (u₁+1))
variable [large_category C]

class strongly_concrete [concrete C] :=
(reflects_isos    : reflects_isos (fibre_functor C))
(preserves_limits : continuous (fibre_functor C))

-- PROJECT
instance type_strongly_concrete : strongly_concrete (Type u₁) := {
    reflects_isos := sorry,
    preserves_limits := begin fsplit, intros, 
    dsimp [fibre_functor, concrete.fibre_functor, universal.cones.functoriality],
   convert L, sorry, sorry
     end
}

end category_theory.universal