-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_categories.monoidal_category

namespace tqft.categories.enriched

open tqft.categories.monoidal_category

structure EnrichedCategory :=
  (V: MonoidalCategory)
  (Obj : Type )
  (Hom : Obj -> Obj -> V^.Obj)
  (compose :  Π ⦃X Y Z : Obj⦄, V^.Hom ((Hom X Y) ⊗ (Hom Y Z)) (Hom X Z))
  -- TODO and so on

-- TODO How would we define an additive category, now? We don't want to say:
--   Hom : Obj -> Obj -> AdditiveGroup
-- instead we want to express something like:
--   Hom : Obj -> Obj -> [something coercible to AdditiveGroup]


end tqft.categories.enriched