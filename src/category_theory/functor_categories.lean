-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .natural_transformation

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

definition {u1 v1 u2 v2} FunctorCategory ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) : Category :=
{
  Obj := Functor C D,
  Hom := λ F G, NaturalTransformation F G,

  identity := λ F, IdentityNaturalTransformation F,
  compose  := @vertical_composition_of_NaturalTransformations C D,

  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition {u1 v1 u2 v2 u3 v3} whiskering_on_left
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} ) :
    Functor (FunctorCategory C D) (FunctorCategory (FunctorCategory D E) (FunctorCategory C E)) :=
{
  onObjects     := λ F, {
    onObjects     := λ G, FunctorComposition F G,
    onMorphisms   := λ _ _ α, whisker_on_left F α,
    identities    := ♯,
    functoriality := ♯
  },
  onMorphisms   := λ F G τ, {
    components := λ H, {
      components := λ c, H.onMorphisms (τ.components c),
      naturality := ♯
    },
    naturality := ♯
  },
  identities    := ♯,
  functoriality := ♯
}

definition {u1 v1 u2 v2 u3 v3} whisker_on_left_functor
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( E : Category.{u3 v3} )
  ( F : Functor C D ) :
  Functor (FunctorCategory D E) (FunctorCategory C E) :=
  (whiskering_on_left C D E).onObjects F

definition {u1 v1 u2 v2 u3 v3} whiskering_on_right
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} ) :
    Functor (FunctorCategory D E) (FunctorCategory (FunctorCategory C D) (FunctorCategory C E)) :=
{
  onObjects     := λ H, {
    onObjects     := λ F, FunctorComposition F H,
    onMorphisms   := λ _ _ α, whisker_on_right α H,
    identities    := ♯,
    functoriality := ♯
  },
  onMorphisms   := λ G H τ, {
    components := λ F, {
      components := λ c, τ.components (F.onObjects c),
      naturality := ♯
    },
    naturality := ♯
  },
  identities    := ♯,
  functoriality := ♯
}

definition {u1 v1 u2 v2 u3 v3} whisker_on_right_functor
  ( C : Category.{u1 v1} )
  { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  ( H : Functor D E ) :
  Functor (FunctorCategory C D) (FunctorCategory C E) :=
(whiskering_on_right C D E).onObjects H

end categories.functor_categories
