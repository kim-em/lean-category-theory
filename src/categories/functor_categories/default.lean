-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..natural_transformation

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u1 v1 u2 v2 u3 v3

definition FunctorCategory (C : Category.{u1 v1}) (D : Category.{u2 v2}) : Category :=
{
  Obj := Functor C D,
  Hom := λ F G, NaturalTransformation F G,

  identity := λ F, IdentityNaturalTransformation F,
  compose  := @vertical_composition_of_NaturalTransformations C D
}

definition whiskering_on_left
  (C : Category.{u1 v1})
  (D : Category.{u2 v2})
  (E : Category.{u3 v3}) :
    Functor (FunctorCategory C D) (FunctorCategory (FunctorCategory D E) (FunctorCategory C E)) :=
{
  onObjects     := λ F, {
    onObjects     := λ G, FunctorComposition F G,
    onMorphisms   := λ _ _ α, whisker_on_left F α
 },
  onMorphisms   := λ F G τ, {
    components := λ H, {
      components := λ c, H.onMorphisms (τ.components c)
   }
 }
}

definition whisker_on_left_functor
  {C : Category.{u1 v1}} {D : Category.{u2 v2}}
  (E : Category.{u3 v3})
  (F : Functor C D) :
  Functor (FunctorCategory D E) (FunctorCategory C E) :=
  (whiskering_on_left C D E).onObjects F

definition whiskering_on_right
  (C : Category.{u1 v1})
  (D : Category.{u2 v2})
  (E : Category.{u3 v3}) :
    Functor (FunctorCategory D E) (FunctorCategory (FunctorCategory C D) (FunctorCategory C E)) :=
{
  onObjects     := λ H, {
    onObjects     := λ F, FunctorComposition F H,
    onMorphisms   := λ _ _ α, whisker_on_right α H,
 },
  onMorphisms   := λ G H τ, {
    components := λ F, {
      components := λ c, τ.components (F.onObjects c)
   }
 }
}

definition whisker_on_right_functor
  (C : Category.{u1 v1})
  {D : Category.{u2 v2}} {E : Category.{u3 v3}}
  (H : Functor D E) :
  Functor (FunctorCategory C D) (FunctorCategory C E) :=
(whiskering_on_right C D E).onObjects H

@[ematch] lemma NaturalTransformation_to_FunctorCategory.components_naturality
  {C : Category.{u1 v1}}
  {D : Category.{u2 v2}}
  {E : Category.{u3 v3}}
  {F G : Functor C (FunctorCategory D E)}
  (T : NaturalTransformation F G) 
  (X : C.Obj)
  {Y Z : D.Obj}
  (f : D.Hom Y Z)
    : E.compose ((F.onObjects X).onMorphisms f) ((T.components X).components Z) =
    E.compose ((T.components X).components Y) ((G.onObjects X).onMorphisms f) :=
begin
  exact (T.components _).naturality _
end

@[ematch] lemma NaturalTransformation_to_FunctorCategory.naturality_components
  {C : Category.{u1 v1}}
  {D : Category.{u2 v2}}
  {E : Category.{u3 v3}}
  {F G : Functor C (FunctorCategory D E)}
  (T : NaturalTransformation F G) 
  (Z : D.Obj)
  {X Y : C.Obj}
  (f : C.Hom X Y)
  : E.compose ((F.onMorphisms f).components Z) ((T.components Y).components Z) =
    E.compose ((T.components X).components Z) ((G.onMorphisms f).components Z) :=
begin
  have p := T.naturality _,
  have q := congr_arg NaturalTransformation.components p,
  tidy,
end

end categories.functor_categories
