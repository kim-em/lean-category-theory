-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal

open categories
open categories.functor
open categories.initial

namespace categories.universal

universes u
variable {C : Type (u+1)}
variable [category C]
variable {D : Type (u+1)}
variable [category D]

structure Continuous (F : C ↝ D) :=
  (preserves_limits : ∀ {J : Type u} [small_category J] (G : J ↝ C) (L : LimitCone G), is_terminal ((Cones_functoriality G F) +> L.terminal_object))

structure Cocontinuous (F : C ↝ D) :=
  (preserves_colimits : ∀ {J : Type u} [small_category J] (G : J ↝ C) (L : ColimitCocone G), is_initial ((Cocones_functoriality G F) +> L.initial_object))

-- PROJECT right adjoints are continuous

end categories.universal

