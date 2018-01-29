-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..creates_limits
import ...examples.semigroups

open categories
open categories.functor
open categories.universal

namespace categories.examples.semigroups

-- example : CreatesProducts ForgetfulFunctor_Semigroups_to_Types := {
--   over := λ I, {
--     cone_from_limit := λ D q, {
--       cone_point := begin sorry end,
--       cone_maps  := sorry
--     },
--     image_of_cone_is_limit_cone := sorry,
--     every_such_cone_is_limit_cone := sorry
--   }
-- }

end categories.examples.semigroups