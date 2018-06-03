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
variable [large_category A]
variable {B : Type (u+1)}
variable [large_category B]

class PreservesLimits (F : Functor A B) :=
(preserves : Π {I : Type u} [small_category I] (D : I ↝ A) (q : LimitCone D), @is_terminal.{u+1 u} (Cone (D ⋙ F)) _ (F.onCones q.terminal_object))

instance HomFunctorPreservesLimits (a : A) : PreservesLimits ((CoYoneda A) +> a) := {
    preserves := λ I D q, sorry
}

instance RepresentableFunctorPreservesLimits (F : A ↝ (Type u)) [Representable F] : PreservesLimits F := sorry

end categories.universal