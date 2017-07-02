-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..full_subcategory
import ..isomorphism

namespace categories.types

open categories
open categories.isomorphism

definition {u} CategoryOfTypes : Category :=
{
    Obj := Type u,
    Hom := λ a b, a → b,

    identity := λ a, id,
    compose  := λ _ _ _ f g, g ∘ f,

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

definition Bijection ( α β : Type ) := Isomorphism CategoryOfTypes α β 

definition Bijection.witness_1 { α β : Type } ( iso : Bijection α β ) ( x : α ) : iso.inverse (iso.morphism x) = x :=
begin
  have p := iso.witness_1,
  exact congr_fun p x,
end
definition Bijection.witness_2 { α β : Type } ( iso : Bijection α β ) ( x : β ) : iso.morphism (iso.inverse x) = x :=
begin
  have p := iso.witness_2,
  exact congr_fun p x,
end

end categories.types
