-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..braided_monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category

namespace tqft.categories.braided_monoidal_category

universe variables u v

@[reducible] definition squared_Braiding { C : MonoidalCategory.{u v} } ( braiding : Braiding C )
  : NaturalTransformation C^.tensor C^.tensor :=
  begin
    pose square := vertical_composition_of_NaturalTransformations braiding^.morphism (whisker_on_left (SwitchProductCategory C C) braiding^.morphism),
    rewrite - FunctorComposition_associative at square,
    erewrite switch_twice_is_the_identity at square,
    rewrite FunctorComposition_left_identity at square,
    exact square
  end 

@[reducible] definition Symmetry(C : BraidedMonoidalCategory) : Prop :=
  squared_Braiding (C^.braiding) = IdentityNaturalTransformation C^.tensor

lemma symmetry_in_terms_of_natural_transformations (C : SymmetricMonoidalCategory): Symmetry C := 
  begin
    blast,
    induction X,
    -- TODO how to get these eq.rec's out of the way?
  end

end tqft.categories.braided_monoidal_category
