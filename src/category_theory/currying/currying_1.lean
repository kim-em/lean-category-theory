-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..natural_transformation
import ..equivalence
import ..products.bifunctors

open categories
open categories.isomorphism
open categories.functor
open categories.equivalence
open categories.functor_categories

namespace categories.natural_transformation

universes u1 v1 u2 v2 u3 v3

variable C : Category.{u1 v1}
variable D : Category.{u2 v2}
variable E : Category.{u3 v3}

definition Uncurry_Functors :
  Functor (FunctorCategory C (FunctorCategory D E)) (FunctorCategory (C × D) E) := 
    {
      onObjects     := λ (F : Functor C (FunctorCategory D E)), {
        onObjects     := λ X, (F.onObjects X.1).onObjects X.2,
        onMorphisms   := λ X Y f, E.compose ((F.onMorphisms f.1).components X.2) ((F.onObjects Y.1).onMorphisms f.2), 
        identities    := ♯,
        functoriality := ♯
      },
      onMorphisms   := λ F G (T : NaturalTransformation F G), {
        components := λ X, (T.components _).components _,
        naturality := ♯ 
      },
      identities    := ♯,
      functoriality := ♯
    }

definition Curry_Functors :
  Functor (FunctorCategory (C × D) E) (FunctorCategory C (FunctorCategory D E)) :=
{
      onObjects     := λ F: Functor (C × D) E, {
        onObjects     := λ X, {
          onObjects     := λ Y, F.onObjects (X, Y),
          onMorphisms   := λ Y Y' g, F.onMorphisms (C.identity X, g),
          identities    := ♯,
          functoriality := ♯
        },
        onMorphisms   := λ X X' f, {
          components := λ Y, F.onMorphisms (f, D.identity Y),
          naturality := ♯
        },
        identities    := ♯,
        functoriality := ♯
      },
      onMorphisms   := λ F G T, {
        components := λ X, {
          components := λ Y, T.components (X, Y),
          naturality := ♯
        },
        naturality := ♯
      },
      identities    := ♯,
      functoriality := ♯
    }

end categories.natural_transformation