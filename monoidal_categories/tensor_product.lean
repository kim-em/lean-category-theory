-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products.associator

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

-- TODO can we avoid these @[reducible]s?
@[reducible] definition TensorProduct ( C: Category ) := Functor ( C × C ) C

definition left_associated_triple_tensor { C : Category.{ u v } } ( tensor : TensorProduct C ) : Functor ((C × C) × C) C :=
  FunctorComposition (tensor × IdentityFunctor C) tensor
definition right_associated_triple_tensor { C : Category.{ u v } } ( tensor : TensorProduct C ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × tensor) tensor

@[reducible] definition Associator { C : Category.{u v} } ( tensor : TensorProduct C ) :=
  NaturalIsomorphism
    (left_associated_triple_tensor tensor)
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor tensor))

@[reducible] definition RightUnitor { C : Category } ( I : C.Obj ) ( tensor : TensorProduct C ) :=
  NaturalIsomorphism
    (FunctorComposition (RightInjectionAt I C) tensor)
    (IdentityFunctor C)

@[reducible] definition LeftUnitor { C : Category } ( I : C.Obj ) ( tensor : TensorProduct C ) :=
  NaturalIsomorphism
    (FunctorComposition (LeftInjectionAt I C) tensor)
    (IdentityFunctor C)

-- TODO all the let statements cause problems later...
@[reducible] definition Pentagon { C : Category } { tensor : TensorProduct C } ( associator : Associator tensor ) :=
  let α ( X Y Z : C.Obj ) := associator ⟨⟨X, Y⟩, Z⟩,
      tensorObjects ( X Y : C.Obj ) := tensor.onObjects ⟨X, Y⟩,
      tensorMorphisms { W X Y Z : C.Obj } ( f : C.Hom W X ) ( g : C.Hom Y Z ) : C.Hom (tensorObjects W Y) (tensorObjects X Z) := tensor.onMorphisms ⟨f, g⟩ in
  ∀ W X Y Z : C.Obj,
    C.compose (C.compose (tensorMorphisms (α W X Y) (C.identity Z)) (α W (tensorObjects X Y) Z)) (tensorMorphisms (C.identity W) (α X Y Z))
  = C.compose (α (tensorObjects W X) Y Z) (α W X (tensorObjects Y Z)) 

@[reducible] definition Triangle { C : Category } { tensor : TensorProduct C } ( I : C.Obj ) ( left_unitor : LeftUnitor I tensor ) ( right_unitor : RightUnitor I tensor ) ( associator : Associator tensor ) :=
  let α ( X Y Z : C.Obj ) := associator ⟨⟨X, Y⟩, Z⟩,
      tensorObjects ( X Y : C.Obj ) := tensor.onObjects ⟨X, Y⟩,
      tensorMorphisms { W X Y Z : C.Obj } ( f : C.Hom W X ) ( g : C.Hom Y Z ) : C.Hom (tensorObjects W Y) (tensorObjects X Z) := tensor.onMorphisms ⟨f, g⟩ in
  ∀ X Y : C.Obj,
    C.compose (α X I Y) (tensorMorphisms (C.identity X) (left_unitor Y))
  = tensorMorphisms (right_unitor X) (C.identity Y)

end tqft.categories.monoidal_category
