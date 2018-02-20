-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..natural_isomorphism

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ u₂ u₃ u₄

variable {B : Type (u₁+1)}
variable [category B]
variable {C : Type (u₂+1)}
variable [category C]
variable {D : Type (u₃+1)}
variable [category D]
variable {E : Type (u₄+1)}
variable [category E]

local attribute [applicable] category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition FunctorComposition_associator
  (F : Functor B C)
  (G : Functor C D)
  (H : Functor D E)
: NaturalIsomorphism (FunctorComposition (FunctorComposition F G) H) (FunctorComposition F (FunctorComposition G H)) := ♯

-- PROJECT pentagon

definition FunctorComposition_left_unitor (F : Functor C D)
: NaturalIsomorphism (FunctorComposition (IdentityFunctor C) F) F := ♯

definition FunctorComposition_right_unitor (F : Functor C D)
: NaturalIsomorphism (FunctorComposition F (IdentityFunctor D)) F := ♯

end categories.functor_categories
