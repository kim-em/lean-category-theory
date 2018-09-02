-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.cones

open category_theory

namespace category_theory.universal

universes u v
variables {C : Type u} [𝒞 : category.{u v} C] {D : Type u} [𝒟 : category.{u v} D]
include 𝒞 𝒟

-- TODO it would be nice to get rid of these explicit universe levels

structure continuous (F : C ↝ D) :=
(preserves_limits : ∀ {J : Type v} [small_category J] (G : J ↝ C) (c : cone G) (L : is_limit c), is_limit ((cones.functoriality G F) c))

structure cocontinuous (F : C ↝ D) :=
(preserves_colimits : ∀ {J : Type v} [small_category J] (G : J ↝ C) (c : cocone G) (L : is_colimit c), is_colimit ((cocones.functoriality G F) c))

-- instance HomFunctorPreservesLimits (a : A) : preserves_limits ((coyoneda A) a) := {
--     preserves := λ I D q, sorry
-- }

-- instance RepresentableFunctorPreservesLimits (F : A ↝ (Type u)) [representable F] : preserves_limits F := sorry


-- PROJECT right adjoints are continuous

end category_theory.universal

