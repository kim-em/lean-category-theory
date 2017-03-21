-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_categories.monoidal_category

namespace tqft.categories.enriched

open tqft.categories.monoidal_category

structure EnrichedCategory :=
  (V: MonoidalCategory)
  (Obj : Type )
  (Hom : Obj → Obj → V^.Obj)
  (compose :  Π { X Y Z : Obj }, V^.Hom (V^.tensorObjects (Hom X Y) (Hom Y Z)) (Hom X Z))
  (identity : Π X : Obj, V^.Hom V^.tensor_unit (Hom X X))
  -- PROJECT and so on



end tqft.categories.enriched