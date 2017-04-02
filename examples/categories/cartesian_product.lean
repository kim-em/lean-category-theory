-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ...monoidal_categories.monoidal_category
import ...discrete_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

@[unfoldable] definition TensorProductOfCategories : TensorProduct CategoryOfCategoriesAndFunctors.{u v} := {
    onObjects     := λ p, ProductCategory p.1 p.2,
    onMorphisms   := λ _ _ p, ProductFunctor p.1 p.2,
    identities    := ♯,
    functoriality := ♮
  }

@[unfoldable] definition CategoryAssociator : Associator TensorProductOfCategories.{u v} := {
    morphism := {
      components := λ t, ProductCategoryAssociator t.1.1 t.1.2 t.2,
      naturality := ♮
    },
    inverse := {
      components := λ t, ProductCategoryInverseAssociator t.1.1 t.1.2 t.2,
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  }

@[unfoldable] definition CategoryTensorUnit := DiscreteCategory.{u v} punit

@[unfoldable] definition CategoryLeftUnitor : @LeftUnitor CategoryOfCategoriesAndFunctors.{u v} CategoryTensorUnit TensorProductOfCategories := {
  morphism := {
    components := λ p, RightProjection _ p,
    naturality := ♮
  },
  inverse := {
    components := λ t, LeftInjectionAt punit.star t,
    naturality := ♮
  },
  witness_1 := begin
                apply NaturalTransformations_componentwise_equal,
                intros C,
                unfold_unfoldable,
                fapply Functors_pointwise_equal,
                -- First show identity on objects:
                simp,
                intros X,
                induction X with X_1 X_2,
                induction X_1,
                dsimp,
                trivial,
                -- Now show identity on morphisms:
                intros X Y f,
                simp,
                induction f with f_1 f_2,
                induction X with X_1 X_2,
                induction X_1,
                induction Y with Y_1 Y_2,
                induction Y_1,
                simp,
                induction f_1 with f_1',
                induction f_1' with f_1'',
                simp at f_1''
               end,
  witness_2 := begin
                apply NaturalTransformations_componentwise_equal,
                intros C,
                unfold_unfoldable,
                fapply Functors_pointwise_equal,
                -- First show identity on objects:
                intros X,
                trivial,
                -- Now show identity on morphisms:
                intros X Y f,
                simp
               end
}

@[unfoldable] definition CategoryRightUnitor : @RightUnitor CategoryOfCategoriesAndFunctors.{u v} CategoryTensorUnit TensorProductOfCategories := {
  morphism := {
    components := λ p, LeftProjection p _,
    naturality := ♮
  },
  inverse := {
    components := λ t, RightInjectionAt punit.star t,
    naturality := ♮
  },
  witness_1 := begin
                apply NaturalTransformations_componentwise_equal,
                intros C,
                unfold_unfoldable,
                fapply Functors_pointwise_equal,
                -- First show identity on objects:
                simp,
                intros X,
                induction X with X_1 X_2,
                induction X_2,
                dsimp,
                trivial,
                -- Now show identity on morphisms:
                intros X Y f,
                simp,
                induction f with f_1 f_2,
                induction X with X_1 X_2,
                induction X_2,
                induction Y with Y_1 Y_2,
                induction Y_2,
                simp,
                induction f_2 with f_2',
                induction f_2' with f_2'',
                simp at f_2''
               end,
  witness_2 := begin
                apply NaturalTransformations_componentwise_equal,
                intros C,
                unfold_unfoldable,
                fapply Functors_pointwise_equal,
                -- First show identity on objects:
                intros X,
                trivial,
                -- Now show identity on morphisms:
                intros X Y f,
                simp
               end
}

@[unfoldable] definition CartesianProductOfCategories : MonoidalStructure CategoryOfCategoriesAndFunctors.{u v} := {
  tensor      := TensorProductOfCategories,
  tensor_unit := CategoryTensorUnit,
  associator_transformation := CategoryAssociator,
  left_unitor  := CategoryLeftUnitor,
  right_unitor := CategoryRightUnitor,
  pentagon := ♯,
  triangle := ♯
}

@[unfoldable] definition SymmetryOnCartesianProductOfCategories : Symmetry CartesianProductOfCategories := {
  braiding             := {
    morphism  := {
      components := λ p, SwitchProductCategory p.1 p.2,
      naturality := ♮
    },
    inverse   := {
      components := λ p, SwitchProductCategory p.2 p.1,
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  },
  hexagon_1 := ♯,
  hexagon_2 := ♯,
  symmetry  := ♯
}

end tqft.categories.monoidal_category