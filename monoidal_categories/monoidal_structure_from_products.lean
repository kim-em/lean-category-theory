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

-- PROJECT

@[pointwise] definition left_associated_triple_Product_projection_1 { C : Category } [ has_FiniteProducts C ] { X Y Z : C.Obj } : C.Hom (product (product X Y).product Z).product X :=
  C.compose (Product.left_projection _) (Product.left_projection _)
@[pointwise] definition left_associated_triple_Product_projection_2 { C : Category } [ has_FiniteProducts C ] { X Y Z : C.Obj } : C.Hom (product (product X Y).product Z).product Y :=
  C.compose (Product.left_projection _) (Product.right_projection _)
@[pointwise] definition right_associated_triple_Product_projection_2 { C : Category } [ has_FiniteProducts C ] { X Y Z : C.Obj } : C.Hom (product X (product Y Z).product).product Y :=
  C.compose (Product.right_projection _) (Product.left_projection _)
@[pointwise] definition right_associated_triple_Product_projection_3 { C : Category } [ has_FiniteProducts C ] { X Y Z : C.Obj } : C.Hom (product X (product Y Z).product).product Z :=
  C.compose (Product.right_projection _) (Product.right_projection _)

-- set_option pp.implicit true

definition MonoidalStructure_from_Products { C : Category } [ has_FiniteProducts C ] : MonoidalStructure C :=
{
    tensor := {
        onObjects     := λ p, (product p.1 p.2).product,
        onMorphisms   := λ X Y f, ((product Y.1 Y.2).map
                                    (C^.compose (product X.1 X.2).left_projection (f.1))
                                    (C^.compose (product X.1 X.2).right_projection (f.2))
                                  ),
        identities    := ♯,
        functoriality := sorry
    },
    tensor_unit := terminal_object,
    associator_transformation := begin
                                   pointwise tactic.skip,
                                   pointwise tactic.skip,
                                   intros,
                                   dsimp,
                                   dunfold_everything' 5,
                                   pointwise tactic.skip,
                                   pointwise tactic.skip,
                                   pointwise tactic.skip,
                                   pointwise tactic.skip,
                                   pointwise tactic.skip,
                                   intros,
                                   dsimp,
                                   unfold_unfoldable,
                                   induction X with X12 X3,
                                   induction X12 with X1 X2,
                                   induction Y with Y12 Y3,
                                   induction Y12 with Y1 Y2,
                                   induction f with f12 f3,
                                   induction f12 with f1 f2,
                                   simp at f1,
                                   simp at f2,
                                   simp at f3,
                                   simp,
                                   force { pointwise tactic.skip },
                                      begin[smt]
                                        eblast
                                      end,
                                      dsimp,
                                      rewrite C.associativity,
                                      rewrite C.associativity,
                                      simp,
                                      rewrite - C.associativity,
                                      rewrite - C.associativity,
                                      simp,
                                      rewrite C.associativity,
                                      simp,
                                      rewrite C.associativity,
                                   force { pointwise tactic.skip },
                                      dsimp,
                                      rewrite C.associativity,
                                      rewrite C.associativity,
                                      
                                      simp,
                                      rewrite - C.associativity,
                                      rewrite - C.associativity,
                                      simp,
                                      rewrite C.associativity,
                                      simp,
                                      rewrite C.associativity,
                                   
                                 end,
    left_unitor               := sorry,
    right_unitor              := sorry,
    pentagon := sorry,
    triangle := sorry
}

-- PROJECT show that this monoidal structure is uniquely braided
-- PROJECT and that braiding is symmetric

end tqft.categories.monoidal_category