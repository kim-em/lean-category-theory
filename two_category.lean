-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.two_category

universe variables u v w

structure StrictTwoCategory :=
  (_0 : Type u)
  (_1 : _0 → _0 → Type v)
  (_2 : Π { X Y : _0 }, _1 X Y → _1 X Y → Type w)
  (identity_0 : Π X : _0, _1 X X)
  (identity_1 : Π { X Y : _0 }, Π f : _1 X Y, _2 f f)
  (compose_1  : Π { X Y Z : _0 }, _1 X Y → _1 Y Z → _1 X Z)
  (compose_2_vertically   : Π { X Y : _0 }, Π { f g h : _1 X Y }, _2 f g → _2 g h → _2 f h)
  (compose_2_horizontally : Π { X Y Z : _0 }, Π { f g : _1 X Y }, Π { h k : _1 Y Z }, _2 f g → _2 h k → _2 (compose_1 f h) (compose_1 g k) )

  (left_identity  : ∀ { X Y : _0 } (f : _1 X Y), compose_1 (identity_0 X) f = f)
  (right_identity : ∀ { X Y : _0 } (f : _1 X Y), compose_1 f (identity_0 Y) = f)
  (associativity_1  : ∀ { W X Y Z : _0 } (f : _1 W X) (g : _1 X Y) (h : _1 Y Z),
    compose_1 (compose_1 f g) h = compose_1 f (compose_1 g h))
  
  -- TODO up_identity, down_identity
  -- TODO associativity_2_vertical, associativity_2_horizontal
  -- TODO interchange

definition CAT : StrictTwoCategory :=
{
    _0 := Category,
    _1 := λ C D, Functor C D,
    _2 := λ _ _ F G, NaturalTransformation F G,
    identity_0 := λ C, IdentityFunctor C,
    identity_1 := λ _ _ F, IdentityNaturalTransformation F,
    compose_1  := λ _ _ _ F G, FunctorComposition F G,
    compose_2_vertically := λ _ _ _ _ _ α β, vertical_composition_of_NaturalTransformations α β,
    compose_2_horizontally := λ _ _ _ _ _ _ _ α β, horizontal_composition_of_NaturalTransformations α β,

    left_identity := λ _ _ F, FunctorComposition_left_identity F,
    right_identity := λ _ _ F, FunctorComposition_right_identity F,
    associativity_1 := λ _ _ _ _ F G H, FunctorComposition_associative F G H
}  

end tqft.categories.two_category