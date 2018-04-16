-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.isomorphism
import categories.types

universe u

open categories
open categories.isomorphism
open categories.types

-- TODO: really here we should be proving that Isomorphism in the category of types is the same notion as equiv.

namespace categories.types

definition Bijection (α β : Type u) := Isomorphism α β 

@[simp] definition Bijection.witness_1 {α β : Type u} (iso : Bijection α β) (x : α) : iso.inverse (iso.morphism x) = x :=
begin
  have p := iso.witness_1_lemma, unfold_projs at p,
  exact congr_fun p x,
end
@[simp] definition Bijection.witness_2 {α β : Type u} (iso : Bijection α β) (x : β) : iso.morphism (iso.inverse x) = x :=
begin
  have p := iso.witness_2_lemma, unfold_projs at p,
  exact congr_fun p x,
end

-- TODO the @s are unpleasant here (ask for help during PR)
@[simp] definition is_Isomorphism_in_Types.witness_1 {α β : Type u} (f : α → β) (h : @is_Isomorphism _ _ α β f) (x : α) : h.inverse (f x) = x :=
begin
  have p := h.witness_1, unfold_projs at p,
  exact congr_fun p x,
end
@[simp] definition is_Isomorphism_in_Types.witness_2 {α β : Type u} (f : α → β) (h : @is_Isomorphism _ _ α β f) (x : β) : f (h.inverse x) = x :=
begin
  have p := h.witness_2, unfold_projs at p,
  exact congr_fun p x,
end

end categories.types