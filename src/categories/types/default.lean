-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..isomorphism
import ..functor

namespace categories.types

open categories
open categories.isomorphism
open categories.functor

universes u v

instance CategoryOfTypes : category (Type u) :=
{
    Hom := λ a b, (a → b),
    identity := λ a, id,
    compose  := λ _ _ _ f g, g ∘ f
}

@[simp] lemma Functor_to_Types_functoriality {C : Type (v+1)} [category C] (F : Functor C (Type u)) {X Y Z : C} (f : Hom X Y) (g : Hom Y Z) (a : F.onObjects X) :
(F.onMorphisms (f ≫ g)) a = (F.onMorphisms g) ((F.onMorphisms f) a) :=
begin
have p := F.functoriality_lemma f g,
tidy
end
@[simp] lemma Functor_to_Types_identities {C : Type (v+1)} [category C] (F : Functor C (Type u)) {X : C} (a : F.onObjects X) :
(F.onMorphisms (𝟙 X)) a = a :=
begin
have p := F.identities_lemma X,
tidy
end

@[applicable] lemma ulift_equal {α : Type v}
  (X Y : ulift.{u v} α)
  (w : X.down = Y.down) : X = Y :=
  begin
    induction X,
    induction Y,
    tidy
  end

definition UniverseLift : Functor (Type u) (Type (u+1)) := {
    onObjects := λ X, ulift.{u+1} X,
    onMorphisms := λ X Y f, λ x : ulift.{u+1} X, ulift.up (f x.down)
}

definition Bijection (α β : Type u) := Isomorphism α β 

@[simp] definition Bijection.witness_1 {α β : Type u} (iso : Bijection α β) (x : α) : iso.inverse (iso.morphism x) = x :=
begin
  have p := iso.witness_1, 
  tidy,
end
@[simp] definition Bijection.witness_2 {α β : Type u} (iso : Bijection α β) (x : β) : iso.morphism (iso.inverse x) = x :=
begin
  have p := iso.witness_2,
  tidy,
end

-- TODO the @s are unpleasant here
@[simp] definition is_Isomorphism_in_Types.witness_1 {α β : Type u} (f : α → β) (h : @is_Isomorphism _ _ α β f) (x : α) : h.inverse (f x) = x :=
begin
  have p := h.witness_1, 
  tidy,
end
@[simp] definition is_Isomorphism_in_Types.witness_2 {α β : Type u} (f : α → β) (h : @is_Isomorphism _ _ α β f) (x : β) : f (h.inverse x) = x :=
begin
  have p := h.witness_2,
  tidy,
end


end categories.types
