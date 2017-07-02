-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

definition ProductCategoryAssociator
  ( C D E: Category )
  : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, (X.1.1, (X.1.2, X.2)),
  onMorphisms   := λ _ _ f, (f.1.1, (f.1.2, f.2)),
  identities    := ♮,
  functoriality := ♮
}

definition ProductCategoryInverseAssociator
  ( C D E: Category )
  : Functor (C × (D × E)) ((C × D) × E) :=
{
  onObjects     := λ X, ((X.1, X.2.1), X.2.2),
  onMorphisms   := λ _ _ f, ((f.1, f.2.1), f.2.2),
  identities    := ♮,
  functoriality := ♮
}

end categories.products
