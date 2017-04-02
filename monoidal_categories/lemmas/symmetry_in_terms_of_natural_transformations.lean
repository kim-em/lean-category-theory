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

@[reducible] definition squared_Braiding { C : Category.{u v} } { m : MonoidalStructure C } ( commutor : Commutor m )
  : NaturalTransformation m.tensor m.tensor :=
  begin
    pose square := vertical_composition_of_NaturalTransformations commutor.morphism (whisker_on_left (SwitchProductCategory C C) commutor.morphism),
    refine ( cast _ square ),
    rewrite - FunctorComposition.associativity,
    erewrite switch_twice_is_the_identity,
    rewrite FunctorComposition.left_identity,
  end 

lemma symmetry_in_terms_of_natural_transformations { C : Category.{u v} } { m : MonoidalStructure C } ( β : Symmetry m ) : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor := 
  begin
    blast,
    induction X,
    unfold squared_Braiding._proof_1,
    blast,
    -- TODO how to get these eq.rec's out of the way?
    exact sorry
  end

end tqft.categories.braided_monoidal_category
