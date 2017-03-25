-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

local attribute [ematch] MonoidalCategory.interchange_right_identity

@[reducible] definition tensor_on_left { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects Z X,
  onMorphisms := λ X Y f, C^.tensorMorphisms (C^.identity Z) f,
  identities := ♮, -- This uses lemma TensorProduct_identities
  functoriality := ♮ -- This uses lemma MonoidalCategory.interchange_right_identity
}

local attribute [ematch] MonoidalCategory.interchange_left_identity

@[reducible] definition tensor_on_right { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects X Z,
  onMorphisms := λ X Y f, C^.tensorMorphisms f (C^.identity Z),
  identities := ♮, -- This uses lemma TensorProduct_identities
  functoriality := ♮ -- This uses lemma MonoidalCategory.interchange_left_identity
}

end tqft.categories.monoidal_category