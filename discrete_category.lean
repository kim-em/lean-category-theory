-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

namespace tqft.categories

structure w { α : Type }( X Y : α ) := ( eq : X = Y )
@[reducible] def w.rfl { α : Type } ( X : α ) : w X X := { eq := rfl }
@[reducible] def w.trans { α : Type} { X Y Z : α } ( a : w X Y ) ( b : w Y Z ) : w X Z := { eq := eq.trans a^.eq b^.eq }

@[pointwise] lemma w_pointwise { α : Type } ( X Y : α ) (w1 : w X Y) (w2 : w X Y) : w1 = w2 := begin induction w1, induction w2, trivial end

definition DiscreteCategory ( α : Type ) : Category :=
{
  Obj      := α,
  Hom      := λ X Y, w X Y,
  identity := λ X, w.rfl X,
  compose  := λ X Y Z f g, w.trans f g,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
>>>>>>> 2687ceb82f0d314c92787be9a87e05ccdf52f005
}

end tqft.categories
