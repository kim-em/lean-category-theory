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

namespace categories.natural_transformation

universes u1 v1 u2 v2 u3 v3

variable C : Category.{u1 v1}
variable D : Category.{u2 v2}
variable E : Category.{u3 v3}

@[ematch] lemma components_naturality -- TODO this should be somewhere more central about functors to functor categories
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  { F G : Functor C (FunctorCategory D E) }
  ( T : NaturalTransformation F G ) 
  ( X : C.Obj )
  { Y Z : D.Obj }
  ( f : D.Hom Y Z )
    : E.compose ((F.onObjects X).onMorphisms f) ((T.components X).components Z) =
    E.compose ((T.components X).components Y) ((G.onObjects X).onMorphisms f) :=
begin
  exact (T.components _).naturality _
end

@[ematch] lemma naturality_components
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  { F G : Functor C (FunctorCategory D E) }
  ( T : NaturalTransformation F G ) 
  ( Z : D.Obj )
  { X Y : C.Obj }
  ( f : C.Hom X Y )
  : E.compose ((F.onMorphisms f).components Z) ((T.components Y).components Z) =
    E.compose ((T.components X).components Z) ((G.onMorphisms f).components Z) :=
begin
  have p := T.naturality _,
  have q := congr_arg NaturalTransformation.components p,
  have r := congr_fun q _,
  tidy,
  rewrite r,
end

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