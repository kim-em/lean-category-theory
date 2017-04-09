-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..monoidal_categories.monoidal_category

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.examples

-- PROJECT none of these proofs work, because we're not using type classes, because type classes don't resolve correctly here.

-- @[unfoldable] definition monoid_as_Category { α : Type } ( m : monoid α ) : Category :=
-- {
--     Obj      := unit,
--     Hom      := λ _ _, α,
--     compose  := λ _ _ _ f g, @monoid.mul α m f g,
--     identity := λ _, one,
--     left_identity  := sorry,
--     right_identity := sorry,
--     associativity  := sorry
-- }

-- definition comm_monoid_as_MonoidalCategory { α : Type } ( m : comm_monoid α ) : MonoidalStructure (monoid_as_Category (@comm_monoid.to_monoid α m)) :=
-- {
--   tensor := {
--     onObjects     := λ _, unit.star,
--     onMorphisms   := λ _ _ p, @comm_monoid.mul α m p.1 p.2,
--     identities    := sorry,
--     functoriality := sorry   
--   },
--   tensor_unit := unit.star,
--   associator_transformation := sorry,
--   left_unitor               := sorry,
--   right_unitor              := sorry,
--   pentagon := sorry,
--   triangle := sorry
-- }

-- structure CategoryWithOneObject extends Category :=
--   ( object  : Obj )
--   ( witness : ∀ X : Obj, X = object )

end tqft.categories.examples