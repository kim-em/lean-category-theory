-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.types
import category_theory.isomorphism
import category_theory.tactics.obviously

open category_theory

universes u v

namespace category_theory.universal

definition is_equiv {α β : Type v} (f : α → β) := @is_iso (Type v) (category_theory.types) _ _ f

@[forward] lemma subtype_val {α : Type u} {P : α → Prop} {x y : {a : α // P a}} (h : x = y) : x.val = y.val := 
begin obviously, end

section shapes
structure shape (C : Type u) [𝒞 : category.{u v} C] :=
(X : C)

@[extensionality] lemma shape.ext (C : Type u) [𝒞 : category.{u v} C] (S T : shape C) (h : S.X = T.X) : S = T :=
begin cases S, cases T, obviously end

structure point (C : Type u) [𝒞 : category.{u v} C] extends shape C.
end shapes

end category_theory.universal
