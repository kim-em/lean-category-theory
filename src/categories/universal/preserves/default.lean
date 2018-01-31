-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.instances
import categories.yoneda

open categories
open categories.functor
open categories.initial
open categories.yoneda
open categories.types

namespace categories.universal

class PreservesLimits { A B : Category } ( F : Functor A B ) :=
( preserves : Π { I : Category } ( D : Functor I A ) ( q : LimitCone D ), @is_terminal (Cones (FunctorComposition D F)) (F.onCones q.terminal_object) )

theorem HomFunctorPreservesLimits { A : Category } ( a : A.Obj ) : PreservesLimits ((CoYoneda A).onObjects a) := {
    preserves := λ I D q, sorry
}

definition RepresentableFunctorPreservesLimits { A : Category } ( F : Functor A CategoryOfTypes ) [ Representable F ] : PreservesLimits F := sorry
attribute [instance] RepresentableFunctorPreservesLimits

end categories.universal