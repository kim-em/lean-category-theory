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

local attribute [reducible] lift_t coe_t coe_b

@[simp] lemma bifunctor_identities
  { C D E : Category }
  ( X : C^.Obj ) ( Y : D^.Obj )
  ( F : Functor (C × D) E ) : @Functor.onMorphisms _ _ F (X, Y) (X, Y) (C^.identity X, D^.identity Y) = E^.identity (F^.onObjects (X, Y)) :=
  begin
    assert p : (C^.identity X, D^.identity Y) = (C × D)^.identity (X, Y), blast,
    rewrite p,
    rewrite F^.identities
  end 

definition tensor_on_left { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects Z X,
  onMorphisms := λ X Y f, C^.tensorMorphisms (C^.identity Z) f,
  identities := begin
                  intros,
                  dsimp [ MonoidalCategory.tensorMorphisms ],
                  assert p : (C^.identity Z, C^.identity X) = (C × C)^.identity (Z, X), blast,
                  rewrite p,
                  rewrite C^.tensor^.identities
                end,
  functoriality := begin
                      blast,
                      -- TODO, why doesn't this work?
                      -- begin[smt]
                      --   eblast_using [ Category.left_identity, MonoidalCategory.interchange ]
                      -- end,
                      rewrite - C^.interchange,
                      rewrite C^.left_identity
                    end
}

definition tensor_on_right { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects X Z,
  onMorphisms := λ X Y f, C^.tensorMorphisms f (C^.identity Z),
  identities := begin
                  intros,
                  dsimp [ MonoidalCategory.tensorMorphisms ],
                  assert p : (C^.identity X, C^.identity Z) = (C × C)^.identity (X, Z), blast,
                  rewrite p,
                  rewrite C^.tensor^.identities
                end,
  functoriality := begin
                      blast,
                      rewrite - C^.interchange,
                      rewrite C^.left_identity
                    end
}

end tqft.categories.monoidal_category