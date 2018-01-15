-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation

open categories
open categories.functor
open categories.natural_transformation

namespace categories.two_category

universe variables u v w

structure StrictTwoCategory :=
  (Hom_0 : Type u)
  (Hom_1 : Hom_0 → Hom_0 → Type v)
  (Hom_2 : Π { X Y : Hom_0 }, Hom_1 X Y → Hom_1 X Y → Type w)
  (identity_0 : Π X : Hom_0, Hom_1 X X)
  (identity_1 : Π { X Y : Hom_0 }, Π f : Hom_1 X Y, Hom_2 f f)
  (compose_1  : Π { X Y Z : Hom_0 }, Hom_1 X Y → Hom_1 Y Z → Hom_1 X Z)
  (compose_2_vertically   : Π { X Y : Hom_0 }, Π { f g h : Hom_1 X Y }, Hom_2 f g → Hom_2 g h → Hom_2 f h)
  (compose_2_horizontally : Π { X Y Z : Hom_0 }, Π { f g : Hom_1 X Y }, Π { h k : Hom_1 Y Z },
     Hom_2 f g → Hom_2 h k → Hom_2 (compose_1 f h) (compose_1 g k) )

  (left_identity  : ∀ { X Y : Hom_0 } (f : Hom_1 X Y), compose_1 (identity_0 X) f = f)
  (right_identity : ∀ { X Y : Hom_0 } (f : Hom_1 X Y), compose_1 f (identity_0 Y) = f)
  (associativity_1  : ∀ { W X Y Z : Hom_0 } (f : Hom_1 W X) (g : Hom_1 X Y) (h : Hom_1 Y Z),
    compose_1 (compose_1 f g) h = compose_1 f (compose_1 g h))
  
  (up_identity : ∀ { X Y : Hom_0 } { f g : Hom_1 X Y } ( α : Hom_2 f g ), compose_2_vertically α (identity_1 g) = α)
  (down_identity : ∀ { X Y : Hom_0 } { f g : Hom_1 X Y } ( α : Hom_2 f g ), compose_2_vertically (identity_1 f) α = α)
  (associativity_2_vertical : ∀ { X Y : Hom_0 } { f g h k : Hom_1 X Y } ( α : Hom_2 f g ) ( β : Hom_2 g h ) ( γ : Hom_2 h k ), 
    compose_2_vertically (compose_2_vertically α β) γ = compose_2_vertically α (compose_2_vertically β γ))
  (associativity_2_horizontal : ∀ { W X Y Z : Hom_0 } { f g : Hom_1 W X } { h k : Hom_1 X Y } { i j : Hom_1 Y Z } ( α: Hom_2 f g ) ( β : Hom_2 h k ) ( γ : Hom_2 i j ), 
    compose_2_horizontally (compose_2_horizontally α β) γ = ⟦ compose_2_horizontally α (compose_2_horizontally β γ) ⟧)
  (interchange : ∀ { X Y Z : Hom_0 } { f g h : Hom_1 X Y } { i j k : Hom_1 Y Z } ( α : Hom_2 f g ) ( β : Hom_2 i j ) ( γ : Hom_2 g h ) ( δ : Hom_2 j k ), 
    compose_2_vertically (compose_2_horizontally α β) (compose_2_horizontally γ δ) =
    compose_2_horizontally (compose_2_vertically α γ) (compose_2_vertically β δ))

attribute [simp] StrictTwoCategory.left_identity StrictTwoCategory.right_identity StrictTwoCategory.up_identity StrictTwoCategory.down_identity
attribute [ematch] StrictTwoCategory.associativity_1 StrictTwoCategory.associativity_2_vertical StrictTwoCategory.associativity_2_horizontal StrictTwoCategory.interchange

local attribute [applicable] Functors_pointwise_equal -- evil

definition CAT : StrictTwoCategory :=
{
    Hom_0 := Category,
    Hom_1 := λ C D, Functor C D,
    Hom_2 := λ _ _ F G, NaturalTransformation F G,
    identity_0 := λ C, IdentityFunctor C,
    identity_1 := λ _ _ F, IdentityNaturalTransformation F,
    compose_1  := λ _ _ _ F G, FunctorComposition F G,
    compose_2_vertically := λ _ _ _ _ _ α β, α ∘̬ β,
    compose_2_horizontally := λ _ _ _ _ _ _ _ α β, α ∘ₕ β,

    left_identity   := ♯,
    right_identity  := ♯,
    associativity_1 := ♮,

    up_identity                := ♯,
    down_identity              := ♯,
    associativity_2_vertical   := ♯,
    associativity_2_horizontal := ♯,
    interchange                := ♯
}  

definition HomCategory ( C : StrictTwoCategory ) ( X Y : C.Hom_0 ) : Category := {
  Obj            := C.Hom_1 X Y,
  Hom            := λ f g, C.Hom_2 f g,
  identity       := λ f, C.identity_1 f,
  compose        := λ _ _ _ α β, C.compose_2_vertically α β
}

-- PROJECT show that HomCategory C X X is (strict) monoidal?

structure DualMorphisms { C : StrictTwoCategory } { X Y : C.Hom_0 } ( f : C.Hom_1 X Y ) ( g : C.Hom_1 Y X ) :=
  ( unit : C.Hom_2 (C.compose_1 f g) (C.identity_0 X) )
  ( counit : C.Hom_2 (C.identity_0 Y) (C.compose_1 g f) )
  -- PROJECT we need to rewrite along associativity_1
  -- ( zigzag_right : C.compose_2_vertically (C.compose_2_horizontally (C.identity_1 f) counit) (C.compose_2_horizontally unit (C.identity_1 f)) = C.identity_1 f)
  -- PROJECT the other zigzag

end categories.two_category