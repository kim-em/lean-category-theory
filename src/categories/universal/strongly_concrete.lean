-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.instances
import categories.universal.preserves
import categories.concrete
import categories.functor.isomorphism

open categories
open categories.functor
open categories.initial
open categories.types

namespace categories.universal

universes u₁
variable (C : Type (u₁+1))
variable [large_category C]

class StronglyConcrete [Concrete C] :=
  (reflects_isos    : ReflectsIsomorphisms (FibreFunctor C))
  (preserves_limits : PreservesLimits (FibreFunctor C))

-- PROJECT
-- instance Types_StronglyConcrete : StronglyConcrete CategoryOfTypes := {
--     F := IdentityFunctor CategoryOfTypes,
--     w := sorry,
--     reflects_isos := sorry,
--     preserves_limits := {
--       preserves := λ I D q, {
--           morphism_to_terminal_object_from := λ c, {
--               cone_morphism := (q.morphism_to_terminal_object_from c).cone_morphism,
--          },
--           uniqueness_of_morphisms_to_terminal_object := sorry
--      }
--    },
--}

end categories.universal