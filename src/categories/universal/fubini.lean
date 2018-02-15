-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .universal
import ..isomorphism
import ..natural_transformation
import ..currying.currying_1

open categories
open categories.functor
open categories.isomorphism
open categories.initial
open categories.natural_transformation

namespace categories.universal

-- structure iterated_limit_for_bifunctor 
--   {J K : Category}
--   {C : Category}
--   (F : Functor (J × K) C) :=
--   (limitFunctor : LimitCone (Curry_Functors J K C F))
  -- (limitObject  : LimitCone (limitFunctor.terminal_object.cone_point))

-- definition Fubini_for_Limits
--   {J K : Category}
--   {C : Category}
--   {F : Functor (J × K) C}
--   (lim : LimitCone F) : iterated_limit_for_bifunctor F := {
--       limitFunctor := {
--           terminal_object := {
--               cone_point    := {
--                   onObjects     := λ k : K.Obj, sorry,
--                   onMorphisms   := λ _ _ f, sorry,
--                   identities    := sorry,
--                   functoriality := sorry
--              },
--               cone_maps     := sorry,
--               commutativity := sorry
--          },
--           morphism_to_terminal_object_from  := sorry,
--           uniqueness_of_morphisms_to_terminal_object := sorry
--      },
--       limitObject  := sorry
--  }

-- definition Fubini_for_Limits_inverse
--   {J K : Category}
--   {C : Category}
--   {F : Functor (J × K) C}
--   (lim : iterated_limit_for_bifunctor F) : Limit F := sorry

-- lemma Fubini_for_Limits.objects_isomorphic
--   {J K : Category}
--   {C : Category}
--   {F : Functor (J × K) C}
--   (lim : Limit F) : Isomorphism C lim.object.limit (Fubini_for_Limits lim).limitObject.object.limit := sorry

-- lemma Fubini_for_Limits_inverse.objects_isomorphic
--   {J K : Category}
--   {C : Category}
--   {F : Functor (J × K) C}
--   (lim : iterated_limit_for_bifunctor F) : Isomorphism C lim.limitObject.object.limit (Fubini_for_Limits_inverse lim).object.limit := sorry

end categories.universal