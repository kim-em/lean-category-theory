-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..natural_isomorphism

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

local attribute [applicable] Category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition {u1 v1 u2 v2 u3 v3 u4 v4} FunctorComposition_associator
  { B : Category.{u1 v1} } { C : Category.{u2 v2} } { D : Category.{u3 v3} } { E : Category.{u4 v4} }
  ( F : Functor B C )
  ( G : Functor C D )
  ( H : Functor D E )
: NaturalIsomorphism (FunctorComposition (FunctorComposition F G) H) (FunctorComposition F (FunctorComposition G H)) := ♯

-- PROJECT these are really slow.
definition {u1 v1 u2 v2} FunctorComposition_left_unitor
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( F : Functor C D )
: NaturalIsomorphism (FunctorComposition (IdentityFunctor C) F) F := 
 by tidy {hints:=[9, 8, 9, 8, 7, 6, 9, 7, 10, 9, 8, 7, 6, 9, 7, 10, 6, 7, 9, 10, 6, 7, 9, 10]}

definition {u1 v1 u2 v2} FunctorComposition_right_unitor
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( F : Functor C D )
: NaturalIsomorphism (FunctorComposition F (IdentityFunctor D) ) F := 
 by tidy {hints:=[9, 8, 9, 8, 7, 6, 9, 7, 10, 9, 8, 7, 6, 9, 7, 10, 6, 7, 9, 10, 6, 7, 9, 10]}

end categories.functor_categories
