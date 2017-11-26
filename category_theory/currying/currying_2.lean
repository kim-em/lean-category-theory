-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .currying_1

open categories
open categories.isomorphism
open categories.functor
open categories.equivalence

namespace categories.natural_transformation

-- lemma simon_1 ( a b : ℕ ) : a + b = b + a := ♯
-- lemma simon_2 ( a : ℕ ) : 0 * a = 0 := begin
--                                           simp, 
--                                        end


-- lemma simons_distrib ( x y z : ℤ ) : x * (y + z) = x * y + x * z := sorry

-- lemma c : 2 * 3 = 6 := by tidy

-- lemma simon_3 ( a b : ℤ ) : ∃ c : ℤ , 3 * a + 6 * b = 3 * c :=
-- begin
--   existsi a + b * 2,
--   rewrite simons_distrib,
--   simp,
--   have p : 2 * 3 = 6, { tidy },
--   tidy,
-- end                                       

universes u1 v1 u2 v2 u3 v3

variable C : Category.{u1 v1}
variable D : Category.{u2 v2}
variable E : Category.{u3 v3}

definition Curry_Uncurry_to_identity
    : NaturalTransformation (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) (IdentityFunctor _) := ♯ 

definition identity_to_Curry_Uncurry
    : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Uncurry_Functors C D E) (Curry_Functors C D E)) := ♯ 

definition Uncurry_Curry_to_identity
    : NaturalTransformation (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) (IdentityFunctor _) := ♯ 
     
definition identity_to_Uncurry_Curry
    : NaturalTransformation (IdentityFunctor _) (FunctorComposition (Curry_Functors C D E) (Uncurry_Functors C D E)) := ♯ 

end categories.natural_transformation