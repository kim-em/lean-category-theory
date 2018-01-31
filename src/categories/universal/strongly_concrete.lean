-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .instances
import .preserves
import ..concrete

open categories
open categories.functor
open categories.initial
open categories.types

namespace categories.universal

structure StronglyConcrete ( C : Category ) extends Concrete C := 
  ( reflects_isos    : ReflectsIsomorphisms F . tidy' )
  ( preserves_limits : PreservesLimits F )

attribute [class] StronglyConcrete

-- instance Types_StronglyConcrete : StronglyConcrete CategoryOfTypes := {
--     F := IdentityFunctor CategoryOfTypes,
--     w := sorry,
--     reflects_isos := sorry,
--     preserves_limits := {
--       preserves := λ I D q, {
--           morphism_to_terminal_object_from := λ c, {
--               cone_morphism := (q.morphism_to_terminal_object_from c).cone_morphism,
--           },
--           uniqueness_of_morphisms_to_terminal_object := sorry
--       }
--     },
-- }

end categories.universal