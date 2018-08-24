-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.cones

open category_theory

namespace category_theory.universal

universes u
variables {C : Type (u+1)} [large_category C] {D : Type (u+1)} [large_category D]

-- TODO it would be nice to get rid of these explicit universe levels

structure continuous (F : C ↝ D) :=
(preserves_limits : ∀ {J : Type u} [small_category J] (G : J ↝ C) (c : cone G) (L : is_limit c), is_limit ((cones.functoriality G F) c))

structure cocontinuous (F : C ↝ D) :=
(preserves_colimits : ∀ {J : Type u} [small_category J] (G : J ↝ C) (L : colimit G), is_initial.{u+1 u} ((cocones.functoriality G F) L.t))

-- instance HomFunctorPreservesLimits (a : A) : preserves_limits ((coyoneda A) a) := {
--     preserves := λ I D q, sorry
-- }

-- instance RepresentableFunctorPreservesLimits (F : A ↝ (Type u)) [representable F] : preserves_limits F := sorry


-- PROJECT right adjoints are continuous

end category_theory.universal

