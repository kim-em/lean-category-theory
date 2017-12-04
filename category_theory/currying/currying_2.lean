-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

-- TODO this was taking forever to compile

-- import .currying_1

-- open categories
-- open categories.isomorphism
-- open categories.functor
-- open categories.equivalence

-- namespace categories.natural_transformation

-- universes u1 v1 u2 v2 u3 v3

-- variable C : Category.{u1 v1}
-- variable D : Category.{u2 v2}
-- variable E : Category.{u3 v3}

-- definition Curry_Uncurry_to_identity
--     : NaturalTransformation (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) (IdentityFunctor _) := ♯ 

-- definition identity_to_Curry_Uncurry
--     : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) := ♯ 

-- definition Uncurry_Curry_to_identity
--     : NaturalTransformation (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) (IdentityFunctor _) := ♯ 
     
-- definition identity_to_Uncurry_Curry
--     : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) := ♯ 

-- end categories.natural_transformation