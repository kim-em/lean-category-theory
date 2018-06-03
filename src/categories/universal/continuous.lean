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
variable [large_category C]
variable {D : Type (u+1)}
variable [large_category D]

-- TODO it would be nice to get rid of these explicit universe levels

structure Continuous (F : C ↝ D) :=
  (preserves_limits : ∀ {J : Type u} [small_category J] (G : J ↝ C) (L : LimitCone G), is_terminal.{u+1 u} ((Cones_functoriality G F) +> L.terminal_object))

structure Cocontinuous (F : C ↝ D) :=
  (preserves_colimits : ∀ {J : Type u} [small_category J] (G : J ↝ C) (L : ColimitCocone G), is_initial.{u+1 u} ((Cocones_functoriality G F) +> L.initial_object))

-- PROJECT right adjoints are continuous

end categories.universal

