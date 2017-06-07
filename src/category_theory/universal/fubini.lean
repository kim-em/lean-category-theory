-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .universal
import ..isomorphism
import ..natural_transformation
import ..graph
import ..currying.currying_1

open tqft.categories
open tqft.categories.functor
open tqft.categories.isomorphism
open tqft.categories.initial
open tqft.categories.natural_transformation

namespace tqft.categories.universal

-- structure iterated_limit_for_bifunctor 
--   { J K : Category }
--   { C : Category }
--   ( F : Functor (J × K) C ) :=
--   ( limitFunctor : Limit (Curry_Functors J K C F) )
--   ( limitObject  : Limit (limitFunctor.object.limit) )

-- -- The dependent sorries here cause a problem described at https://github.com/leanprover/lean/issues/1650
-- definition Fubini_for_Limits
--   { J K : Category }
--   { C : Category }
--   { F : Functor (J × K) C }
--   ( lim : Limit F ) : iterated_limit_for_bifunctor F := {
--       limitFunctor := {
--           object     := {
--               limit         := {
--                   onObjects     := λ k : K.Obj, sorry,
--                   onMorphisms   := λ _ _ f, sorry,
--                   identities    := sorry,
--                   functoriality := sorry
--               },
--               maps          := sorry,
--               commutativity := sorry
--           },
--           morphisms  := sorry,
--           uniqueness := sorry
--       },
--       limitObject  := sorry
--   }

-- definition Fubini_for_Limits_inverse
--   { J K : Category }
--   { C : Category }
--   { F : Functor (J × K) C }
--   ( lim : iterated_limit_for_bifunctor F ) : Limit F := sorry

-- lemma Fubini_for_Limits.objects_isomorphic
--   { J K : Category }
--   { C : Category }
--   { F : Functor (J × K) C }
--   ( lim : Limit F ) : Isomorphism C lim.object.limit (Fubini_for_Limits lim).limitObject.object.limit := sorry

-- lemma Fubini_for_Limits_inverse.objects_isomorphic
--   { J K : Category }
--   { C : Category }
--   { F : Functor (J × K) C }
--   ( lim : iterated_limit_for_bifunctor F ) : Isomorphism C lim.limitObject.object.limit (Fubini_for_Limits_inverse lim).object.limit := sorry

end tqft.categories.universal