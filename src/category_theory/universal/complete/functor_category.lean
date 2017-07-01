-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..complete

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.initial

namespace categories.universal

private definition evaluate_Functor_to_FunctorCategory { J C D : Category } ( F : Functor J (FunctorCategory C D )) ( c : C.Obj ) : Functor J D := {
  onObjects     := λ j, (F.onObjects j).onObjects c,
  onMorphisms   := λ _ _ f, (F.onMorphisms f).components c,
  identities    := ♯,
  functoriality := ♯ 
}

private definition evaluate_Functor_to_FunctorCategory_on_Morphism { J C D : Category } ( F : Functor J (FunctorCategory C D )) ( c c' : C.Obj ) ( f : C.Hom c c' )
  : NaturalTransformation (evaluate_Functor_to_FunctorCategory F c) (evaluate_Functor_to_FunctorCategory F c') := {
    components := λ j, (F.onObjects j).onMorphisms f,
    naturality := ♯ 
  }

-- PROJECT
-- instance Limits_in_FunctorCategory ( C D : Category ) [ cmp : Complete D ] : Complete (FunctorCategory C D) := {
--   limitCone := λ J F, {
--     object     := {
--       -- TODO the whole definition of limit should come down to the fact that limits are functorial
--       limit         := {
--         onObjects     := λ c, limit (evaluate_Functor_to_FunctorCategory F c),
--         onMorphisms   := λ c c' f, sorry,
--         identities    := sorry,
--         functoriality := sorry
--       },
--       maps          := sorry,
--       commutativity := sorry
--     },
--     morphisms  := sorry,
--     uniqueness := sorry
--   }
-- }

end categories.universal