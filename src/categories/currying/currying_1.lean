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

universes u₁ u₂ u₃

variables (C : Type u₁) (D : Type u₂) (E : Type u₃)
variables [category C] [category D] [category E]

definition Uncurry_Functors :
  Functor (Functor C (Functor D E)) (Functor (C × D) E) := 
    {
      onObjects     := λ (F : Functor C (Functor D E)), {
        onObjects     := λ X, (F.onObjects X.1).onObjects X.2,
        onMorphisms   := λ X Y f, ((F.onMorphisms f.1).components X.2) >> ((F.onObjects Y.1).onMorphisms f.2)
     },
      onMorphisms   := λ F G (T : NaturalTransformation F G), {
        components := λ X, (T.components _).components _
     }
   }

definition Curry_Functors :
  Functor (Functor (C × D) E) (Functor C (Functor D E)) :=
{
      onObjects     := λ F: Functor (C × D) E, {
        onObjects     := λ X, {
          onObjects     := λ Y, F.onObjects (X, Y),
          onMorphisms   := λ Y Y' g, F.onMorphisms (𝟙 X, g)
       },
        onMorphisms   := λ X X' f, {
          components := λ Y, F.onMorphisms (f, 𝟙 Y)
       }
     },
      onMorphisms   := λ F G T, {
        components := λ X, {
          components := λ Y, T.components (X, Y)
       }
     }
   }

end categories.natural_transformation