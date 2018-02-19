-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.cones
import categories.yoneda

open categories
open categories.functor
open categories.initial
open categories.yoneda
open categories.types

namespace categories.universal

universes u v w

variable {A : Type (u+1)}
variable [category A]
variable {B : Type (v+1)}
variable [category B]

class PreservesLimits (F : Functor A B) :=
(preserves : Π {I : Type (w+1)} [category I] (D : Functor I A) (q : LimitCone D), @is_terminal (Cone (FunctorComposition D F)) _ (F.onCones q.terminal_object))

theorem HomFunctorPreservesLimits (a : A) : PreservesLimits ((CoYoneda A).onObjects a) := {
    preserves := λ I D q, sorry
}

definition RepresentableFunctorPreservesLimits (F : Functor A (Type u)) [Representable F] : PreservesLimits F := sorry
attribute [instance] RepresentableFunctorPreservesLimits

end categories.universal