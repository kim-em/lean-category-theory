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
  (compose_2_horizontally : Π { X Y Z : _0 }, Π { f g : _1 X Y }, Π { h k : _1 Y Z },
     _2 f g → _2 h k → _2 (compose_1 f h) (compose_1 g k) )

  (left_identity  : ∀ { X Y : _0 } (f : _1 X Y), compose_1 (identity_0 X) f = f)
  (right_identity : ∀ { X Y : _0 } (f : _1 X Y), compose_1 f (identity_0 Y) = f)
  (associativity_1  : ∀ { W X Y Z : _0 } (f : _1 W X) (g : _1 X Y) (h : _1 Y Z),
    compose_1 (compose_1 f g) h = compose_1 f (compose_1 g h))
  
  (up_identity : ∀ { X Y : _0 } { f g : _1 X Y } ( α : _2 f g ), compose_2_vertically α (identity_1 g) = α)
  (down_identity : ∀ { X Y : _0 } { f g : _1 X Y } ( α : _2 f g ), compose_2_vertically (identity_1 f) α = α)
  (associativity_2_vertical : ∀ { X Y : _0 } { f g h k : _1 X Y } ( α : _2 f g ) ( β : _2 g h ) ( γ : _2 h k ), 
    compose_2_vertically (compose_2_vertically α β) γ = compose_2_vertically α (compose_2_vertically β γ))
  (associativity_2_horizontal : ∀ { W X Y Z : _0 } { f g : _1 W X } { h k : _1 X Y } { i j : _1 Y Z } ( α: _2 f g ) ( β : _2 h k ) ( γ : _2 i j ), 
    compose_2_horizontally (compose_2_horizontally α β) γ = ⟦ compose_2_horizontally α (compose_2_horizontally β γ) ⟧)
  (interchange : ∀ { X Y Z : _0 } { f g h : _1 X Y } { i j k : _1 Y Z } ( α : _2 f g ) ( β : _2 i j ) ( γ : _2 g h ) ( δ : _2 j k ), 
    compose_2_vertically (compose_2_horizontally α β) (compose_2_horizontally γ δ) =
    compose_2_horizontally (compose_2_vertically α γ) (compose_2_vertically β δ))

attribute [simp] StrictTwoCategory.left_identity StrictTwoCategory.right_identity StrictTwoCategory.up_identity StrictTwoCategory.down_identity
attribute [ematch] StrictTwoCategory.associativity_1 StrictTwoCategory.associativity_2_vertical StrictTwoCategory.associativity_2_horizontal StrictTwoCategory.interchange

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

    left_identity   := ♮,
    right_identity  := ♮,
    associativity_1 := ♮,

    up_identity                := ♮,
    down_identity              := ♮,
    associativity_2_vertical   := ♮,
    associativity_2_horizontal := ♮,
    interchange                := ♮
}  

definition HomCategory ( C : StrictTwoCategory ) ( X Y : C^._0 ) : Category := {
  Obj            := C^._1 X Y,
  Hom            := λ f g, C^._2 f g,
  identity       := λ f, C^.identity_1 f,
  compose        := λ _ _ _ α β, C^.compose_2_vertically α β,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

-- TODO show that HomCategory C X X is monoidal?

end tqft.categories.two_category