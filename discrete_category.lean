-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

namespace tqft.categories

-- TODO extending Category to work with Sort breaks other things.

-- definition DiscreteCategory ( α : Type ) : Category :=
-- {
--   Obj      := α,
--   Hom      := λ X Y, X = Y,
--   identity := λ X, rfl,
--   compose  := λ X Y Z f g, eq.trans f g,
--   left_identity  := ♮,
--   right_identity := ♮,
--   associativity  := ♮
-- }

set_option pp.implicit true

--lemma emptyExFalso {c : Sort*} (h : empty) : c :=
--@false.elim c (empty.rec_on (λ_, false) h)

definition DiscreteCategory ( α : Type ) [ c : decidable_eq α ] : Category :=
{
  Obj      := α,
  Hom      := λ X Y, if X = Y then unit else empty,
  identity := λ X, match c X X with
                     | is_true  hc  := ()
                     | is_false hnc := absurd rfl hnc
                   end,
  compose  := λ X Y Z f g,
                match (c X Z), (c X Y), (c Y Z) with
                  | (is_true hxz), _, _  -- Is this sufficient? Does the inability to find an element of empty mean the bad cases can't show up?
                      := ()
                  | (is_false hnxz), (is_false hnxy), _
                      := @auto_cast _ _ (if_neg hnxy) f
                  | (is_false hnxz), _, (is_false hnyz)
                      := @auto_cast _ _ (if_neg hnyz) g
                  | (is_false hnxz), (is_true hxy), (is_true hyz)
                      := absurd (eq.trans hxy hyz) hnxz
                end,
  left_identity  := sorry,
  right_identity := sorry,
  associativity  := sorry
}

end tqft.categories
