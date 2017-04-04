-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoids

open tqft.categories
open tqft.categories.functor
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

-- set_option pp.max_steps 50000
-- set_option pp.implicit true
-- set_option pp.universes true
-- set_option pp.coercions true
-- set_option pp.all true
-- set_option pp.implicit false

-- local attribute [elab_simple] prod.mk

definition CategoryOfFreeModules { C : Category } { m : MonoidalStructure C } ( A : MonoidObject m ) : Category :=
{
  Obj := C.Obj,
  Hom := λ X Y, C.Hom X (m.tensorObjects A.object Y),
  identity := λ X, C.compose (m.left_unitor.inverse.components X) (m.tensorMorphisms A.unit (C.identity X)),
  compose := λ _ _ Z f g, C.compose (C.compose (C.compose f (m.tensorMorphisms (C.identity A.object) g)) (m.inverse_associator A.object A.object Z)) (m.tensorMorphisms A.multiplication (C.identity Z)),
  left_identity := begin
                    -- PROJECT dealing with associativity here is quite tedious.
                    -- PROJECT this is a great example problem for clever automation.
                    -- A human quickly sees that we need to combine A.unit and A.multiplication to make them cancel,
                    -- and then performs the necessary rewrites to get there.
                    intros,
                    dsimp,
                    rewrite C.associativity,
                    rewrite C.associativity,
                    rewrite C.associativity,
                    erewrite - C.associativity (m.tensorMorphisms A.unit (C.identity X)),
                    rewrite - m.interchange_identities,
                    rewrite C.associativity,
                    rewrite - C.associativity (m.tensorMorphisms A.unit (C.identity (m.tensorObjects A.object Y))),
                    rewrite - m.tensor.identities,
                    erewrite m.inverse_associator_naturality_0 A.unit (C.identity A.object) (C.identity Y),
                    erewrite C.associativity,
                    erewrite - m.interchange,
                    rewrite A.left_identity, -- <<--- here is the only interesting step!
                    simp, dsimp,
                    erewrite C.right_identity,
                    erewrite - C.associativity,
                    erewrite - m.left_unitor.inverse.naturality,
                    dunfold IdentityFunctor, dsimp,
                    erewrite C.associativity,
                    -- PROJECT this needs Proposition 2.2.4 of Etingof's "Tensor Categories" to finish; and that seems awkward to prove in our setup!
                    exact sorry
                   end,
  right_identity := sorry,
  associativity := sorry
}

-- PROJECT show that after idempotent completing the category of free modules we get the category of modules??
-- PROJECT bimodules
-- PROJECT commutative algebras; modules give bimodules

end tqft.categories.internal_objects