-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import .braided_monoidal_category
import ..universal.universal

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category
open tqft.categories.universal

namespace tqft.categories.monoidal_category

@[reducible,pointwise] definition left_associated_triple_Product_projection_1 { C : Category } [ has_FiniteProducts C ] { X Y Z : C.Obj } : C.Hom (product (product X Y).product Z).product X :=
  C.compose (Product.left_projection _) (Product.left_projection _)
@[reducible,pointwise] definition left_associated_triple_Product_projection_2 { C : Category } [ has_FiniteProducts C ] { X Y Z : C.Obj } : C.Hom (product (product X Y).product Z).product Y :=
  C.compose (Product.left_projection _) (Product.right_projection _)
@[reducible,pointwise] definition right_associated_triple_Product_projection_2 { C : Category } [ has_FiniteProducts C ] { X Y Z : C.Obj } : C.Hom (product X (product Y Z).product).product Y :=
  C.compose (Product.right_projection _) (Product.left_projection _)
@[reducible,pointwise] definition right_associated_triple_Product_projection_3 { C : Category } [ has_FiniteProducts C ] { X Y Z : C.Obj } : C.Hom (product X (product Y Z).product).product Z :=
  C.compose (Product.right_projection _) (Product.right_projection _)

@[simp] lemma left_factorisation_associated_1 { C : Category } [ has_FiniteProducts C ] { W X Y Z : C.Obj } 
  ( h : C.Hom W Z ) ( f : C.Hom Z X ) ( g : C.Hom Z Y ) : C.compose (C.compose h ((product X Y).map f g)) (product X Y).left_projection = C.compose h f :=
  begin rewrite C.associativity, simp end
@[simp] lemma left_factorisation_associated_2 { C : Category } [ has_FiniteProducts C ] { W X Y Z : C.Obj } 
  ( h : C.Hom X W ) ( f : C.Hom Z X ) ( g : C.Hom Z Y ) : C.compose ((product X Y).map f g) (C.compose (product X Y).left_projection h) = C.compose f h :=
  begin rewrite - C.associativity, simp end
@[simp] lemma right_factorisation_associated_1 { C : Category } [ has_FiniteProducts C ] { W X Y Z : C.Obj } 
  ( h : C.Hom W Z ) ( f : C.Hom Z X ) ( g : C.Hom Z Y ) : C.compose (C.compose h ((product X Y).map f g)) (product X Y).right_projection = C.compose h g :=
  begin rewrite C.associativity, simp end
@[simp] lemma right_factorisation_associated_2 { C : Category } [ has_FiniteProducts C ] { W X Y Z : C.Obj } 
  ( h : C.Hom Y W ) ( f : C.Hom Z X ) ( g : C.Hom Z Y ) : C.compose ((product X Y).map f g) (C.compose (product X Y).right_projection h) = C.compose g h :=
  begin rewrite - C.associativity, simp end

definition TensorProduct_from_Products ( C : Category ) [ has_FiniteProducts C ] : TensorProduct C := {
    onObjects     := λ p, (product p.1 p.2).product,
    onMorphisms   := λ X Y f, ((product Y.1 Y.2).map
                                (C.compose (product X.1 X.2).left_projection (f.1))
                                (C.compose (product X.1 X.2).right_projection (f.2))
                              ),
    identities    := ♯,
    functoriality := ♯
}

local attribute [simp] Category.associativity

definition Associator_for_Products ( C : Category ) [ has_FiniteProducts C ] : Associator (TensorProduct_from_Products C) :=
begin
  tidy,
end

end tqft.categories.monoidal_category