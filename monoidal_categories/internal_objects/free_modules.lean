-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoids

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

-- set_option pp.max_steps 50000
-- set_option pp.implicit true
-- set_option pp.universes true
-- set_option pp.coercions true
set_option pp.all true
set_option pp.implicit false

definition CategoryOfFreeModules { C : MonoidalCategory } ( A : MonoidObject C ) : Category :=
{
  Obj := C^.Obj,
  Hom := λ X Y, C^.Hom X (C^.tensorObjects A^.object Y),
  identity := λ X, C^.compose (C^.left_unitor_is_isomorphism^.inverse X) (C^.tensorMorphisms A^.unit (C^.identity X)),
  compose := λ _ _ Z f g, C^.compose (C^.compose (C^.compose f (C^.tensorMorphisms (C^.identity A^.object) g)) (C^.inverse_associator A^.object A^.object Z)) (C^.tensorMorphisms A^.multiplication (C^.identity Z)),
  left_identity := begin
                    -- PROJECT dealing with associativity here is quite tedious.
                    -- PROJECT this is a great example problem for clever automation.
                    -- A human quickly sees that we need to combine A^.unit and A^.multiplication to make them cancel,
                    -- and then performs the necessary rewrites to get there.
                    intros,
                    dsimp,
                    rewrite C^.associativity,
                    rewrite C^.associativity,
                    rewrite C^.associativity,
                    rewrite - C^.associativity (C^.tensorMorphisms A^.unit (C^.identity X)),
                    rewrite - MonoidalCategory.interchange_identities,
                    rewrite C^.associativity,
                    rewrite - C^.associativity (MonoidalCategory.tensorMorphisms C (A^.unit) (C^.identity ((C^.tensor)^.onObjects (A^.object, Y)))),
                    -- We can't just rewrite along - C^.tensor^.identities, because it is confused about C as a category vs C as a monoidal category?
                    rewrite - TensorProduct.identities,
                    dsimp,
                    -- FIXME waiting on https://groups.google.com/d/msg/lean-user/epIwoOxtUn8/a8II-QBMCgAJ
                    rewrite MonoidalCategory.inverse_associator_naturality_0 A^.unit (C^.identity A^.object) (C^.identity Y),
                    
                    exact sorry
                   end,
  right_identity := sorry,
  associativity := sorry
}

-- PROJECT show that after idempotent completing the category of free modules we get the category of modules??
-- PROJECT bimodules
-- PROJECT commutative algebras; modules give bimodules

end tqft.categories.internal_objects