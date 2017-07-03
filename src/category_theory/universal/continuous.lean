-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .universal

open categories
open categories.functor
open categories.initial

namespace categories.universal

structure Continuous { C D : Category } ( F : Functor C D ) :=
  ( preserves_limit : ∀ ( J : Category ) ( G : Functor J C ) ( L : LimitCone G ), is_terminal ((Cones_functoriality G F).onObjects L.terminal_object) )

-- PROJECT left adjoints are continuous

-- PROJECT creating limits

end categories.universal

