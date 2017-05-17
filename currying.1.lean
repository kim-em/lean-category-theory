-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .currying

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor
open tqft.categories.equivalence

namespace tqft.categories.natural_transformation

-- theorem {u1 v1 u2 v2 u3 v3} Currying_for_functors
--   ( C : Category.{u1 v1} )
--   ( D : Category.{u2 v2} )
--   ( E : Category.{u3 v3} ) :
--   Equivalence (FunctorCategory C (FunctorCategory D E)) (FunctorCategory (C × D) E) := 
--   {
--     functor := Uncurry_Functors C D E,
--     inverse := Curry_Functors C D E,
--     isomorphism_1 := begin tidy, admit end,
--     isomorphism_2 := begin tidy, admit end
--   }

end tqft.categories.natural_transformation