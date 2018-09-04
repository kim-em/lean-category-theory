-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.cones

open category_theory

namespace category_theory.limits

universes u v 

variables {C : Type u} [category.{u v} C] {J : Type v} [small_category J] [has_limits.{u v} C] 

def lim : (J ⥤ C) ⥤ C := 
{ obj := limit,
  map' := λ F F' t, (limit.universal_property F').lift $
    { X := limit F, π := λ j, limit.π F j ≫ t j },
  map_id' := begin tidy, erw limit.lift_π, dsimp, simp, end }. -- FIXME why doesn't simp use limit.lift_π here?
 
-- boilerplate
@[simp] lemma lim_map [has_limits.{u v} C] {F F' : J ⥤ C} (t : F ⟹ F') : 
  lim.map t = ((limit.universal_property F').lift $ { X := limit F, π := λ j, limit.π F j ≫ t j }) :=
rfl

-- def colim : (J ⥤ C) ⥤ C := 
-- { obj := colimit,
--   map' := λ F F' t, (colimit.universal_property F').desc $
--     { X := colimit F, π := λ j, t j ≫ colimit.ι F j},
--   map_id' := begin tidy, erw colimit.desc_ι, dsimp, simp, end }. -- FIXME why doesn't simp work here?

end category_theory.limits