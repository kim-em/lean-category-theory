-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .category
import .functor
import .natural_transformation
import .products
import .monoidal_category

namespace tqft.categories.braided_monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.monoidal_category

universe variables u v

definition Braiding(C : MonoidalCategory.{u v}) := 
  NaturalIsomorphism (C^.tensor) (FunctorComposition (SwitchProductCategory C^.to_LaxMonoidalCategory^.to_PreMonoidalCategory^.to_Category C) C^.tensor)

structure BraidedMonoidalCategory
  extends parent: MonoidalCategory :=
  (braiding: Braiding parent)

instance BraidedMonoidalCategory_coercion_to_MonoidalCategory : has_coe BraidedMonoidalCategory MonoidalCategory := ⟨BraidedMonoidalCategory.to_MonoidalCategory⟩

definition squared_Braiding { C : MonoidalCategory.{u v} } ( braiding : Braiding C )
  : NaturalTransformation C^.tensor C^.tensor :=
  begin
    pose square := vertical_composition_of_NaturalTransformations braiding^.morphism (whisker_on_left (SwitchProductCategory C C) braiding^.morphism),
    rewrite - FunctorComposition_associative at square,
    erewrite switch_twice_is_the_identity at square,
    rewrite FunctorComposition_left_identity at square,
    exact square
  end 

definition Symmetry(C : BraidedMonoidalCategory) : Prop :=
  squared_Braiding (C^.braiding) = IdentityNaturalTransformation C^.tensor

structure SymmetricMonoidalCategory
  extends parent: BraidedMonoidalCategory :=
  (symmetry: Symmetry parent)

end tqft.categories.braided_monoidal_category