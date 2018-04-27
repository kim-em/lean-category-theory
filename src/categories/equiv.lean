-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.category
import categories.isomorphism
import categories.functor
import categories.natural_transformation

namespace categories.types

open categories
open categories.isomorphism
open categories.functor

universes u v w

instance CategoryOfEquivalences : category (Type u) :=
{ Hom            := λ a b, equiv a b,
  identity       := λ a, equiv.refl a,
  compose        := λ _ _ _ f g, equiv.trans f g, 
  left_identity := sorry,
  right_identity := sorry,
  associativity := sorry }

class canonical_equiv (α : Sort*) (β : Sort*) extends equiv α β.

class transportable (f : Type u → Type u) := 
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

-- Finally a command like: `initialize_transport group` would create the next two declarations automagically:

def group.transportable : transportable group := sorry
instance group.transport {α β : Type u} [R : group α] [e : canonical_equiv α β] : group β := (@transportable.on_equiv group group.transportable _ _ e.to_equiv).to_fun R

end categories.types