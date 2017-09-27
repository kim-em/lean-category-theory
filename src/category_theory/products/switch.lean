-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products
import ..natural_isomorphism

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

definition SwitchProductCategory ( C D : Category ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X.snd, X.fst),
  onMorphisms   := λ _ _ f, (f.snd, f.fst),
  identities    := ♮,
  functoriality := ♮
}

definition SwitchSymmetry
  ( C D : Category )
    : NaturalIsomorphism (FunctorComposition (SwitchProductCategory C D) (SwitchProductCategory D C)) (IdentityFunctor (C × D)) :=
    by tidy {hints:=[9, 8, 9, 8, 6, 2, 7, 6, 9, 10, 9, 10, 9, 8, 6, 2, 7, 6, 9, 10, 9, 10, 2, 6, 7, 6, 9, 10, 9, 10, 2, 6, 7, 6, 9, 10, 9, 10]}
    
end categories.products
