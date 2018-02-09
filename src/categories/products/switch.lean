-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products
import ..natural_isomorphism

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

local attribute [applicable] Category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

definition SwitchProductCategory (C D : Category) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X.snd, X.fst),
  onMorphisms   := λ _ _ f, (f.snd, f.fst)
}

definition SwitchSymmetry
  (C D : Category)
    : NaturalIsomorphism (FunctorComposition (SwitchProductCategory C D) (SwitchProductCategory D C)) (IdentityFunctor (C × D)) := ♯
        
end categories.products
