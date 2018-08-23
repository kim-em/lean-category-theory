-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.cones
import category_theory.representable

open category_theory
open category_theory.initial
open category_theory.yoneda

namespace category_theory.universal

universes u v w

-- TODO think harder about universes here
variables {A : Type (u+1)} [large_category A] {B : Type (u+1)}  [large_category B]

class preserves_limits (F : A ↝ B) :=
(preserves : Π {I : Type u} [small_category I] (D : I ↝ A) (q : LimitCone D), @is_terminal.{u+1 u} (Cone (D ⋙ F)) _ (F.on_cone q.obj))

instance HomFunctorPreservesLimits (a : A) : preserves_limits ((coyoneda A) a) := {
    preserves := λ I D q, sorry
}

instance RepresentableFunctorPreservesLimits (F : A ↝ (Type u)) [representable F] : preserves_limits F := sorry

end category_theory.universal