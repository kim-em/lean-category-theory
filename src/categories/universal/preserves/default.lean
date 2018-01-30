-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.instances

open categories
open categories.functor
open categories.initial

namespace categories.universal

class PreservesLimits { A B : Category } ( F : Functor A B ) :=
( preserves : Π { I : Category } ( D : Functor I A ) ( q : LimitCone D ), @is_terminal (Cones (FunctorComposition D F)) (F.onCones q.terminal_object) )

end categories.universal