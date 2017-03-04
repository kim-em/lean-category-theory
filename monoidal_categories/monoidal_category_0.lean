-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products

--set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

@[reducible] definition TensorProduct ( C: Category ) := Functor ( C × C ) C

@[reducible] definition left_associated_triple_tensor { C : Category.{ u v } } ( tensor : TensorProduct C ) : Functor ((C × C) × C) C :=
  FunctorComposition (tensor × IdentityFunctor C) tensor
@[reducible] definition right_associated_triple_tensor { C : Category.{ u v } } ( tensor : TensorProduct C ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × tensor) tensor

@[reducible] definition Associator { C : Category.{ u v } } ( tensor : TensorProduct C ) := 
  NaturalTransformation 
    (left_associated_triple_tensor tensor) 
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor tensor))

definition Pentagon { C : Category } { tensor : TensorProduct C } ( associator : Associator tensor ) :=
  let α ( X Y Z : C^.Obj ) := associator ((X, Y), Z) in
  let tensorObjects ( X Y : C^.Obj ) := tensor^.onObjects (X, Y) in
  let tensorMorphisms { W X Y Z : C^.Obj } ( f : C^.Hom W X ) ( g : C^.Hom Y Z ) : C^.Hom (tensorObjects W Y) (tensorObjects X Z) := tensor^.onMorphisms (f, g) in
  ∀ W X Y Z : C^.Obj, 
    C^.compose (α (tensorObjects W X) Y Z) (α W X (tensorObjects Y Z))
  = C^.compose (C^.compose (tensorMorphisms (α W X Y) (C^.identity Z)) (α W (tensorObjects X Y) Z)) (tensorMorphisms (C^.identity W) (α X Y Z)) 

end tqft.categories.monoidal_category
