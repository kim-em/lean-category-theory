-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

namespace categories.util

inductive {u} hlist : list (Type u) → Type (u+1)
| nil  : hlist []
| cons : Π {α : Type u} {l : list (Type u)}, α → hlist l → hlist (α::l)

notation a :: b := hlist.cons a b
notation `[` l:(foldr `, ` (h t, hlist.cons h t) hlist.nil `]`) := l

definition hlist.indexed_map { α : Type } { Z W : α → Type } ( f : Π { a : α } ( z : Z a ), W a ) : Π ( X : list α ), hlist (X.map Z) → hlist (X.map W)
| list.nil hlist.nil := hlist.nil
| (list.cons a X) (hlist.cons z H) := hlist.cons (f z) (hlist.indexed_map X H)

-- PROJECT perhaps someone has already done this?
-- definition {u} hlist.zip : Π { α β : list (Type u) } ( L : hlist α ) ( R: hlist β ), hlist ((α.zip β).map (λ p, p.1 × p.2)) 
-- | _ list.nil _ hlist.nil := hlist.nil
-- | list.nil _ hlist.nil _ := hlist.nil

end categories.util