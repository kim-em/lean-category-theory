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

@[reducible] definition {u v} squared_Braiding { C : Category.{u v} } { m : MonoidalStructure C } ( commutor : Commutor m )
  : NaturalTransformation m.tensor m.tensor :=
  begin
   exact (commutor.morphism
           ∘̬ (whisker_on_left (SwitchProductCategory C C) commutor.morphism)
           ∘̬ (FunctorComposition_associator _ _ _).inverse
           ∘̬ (whisker_on_right (SwitchSymmetry _ _).morphism m.tensor)
           ∘̬ (FunctorComposition_left_unitor m.tensor).morphism)
  end 

lemma {u v} symmetry_in_terms_of_natural_transformations { C : Category.{u v} } { m : MonoidalStructure C } ( β : Symmetry m ) : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor := 
  begin
    tidy
  end

lemma {u v} symmetric_in_terms_of_components { C : Category.{u v} } { m : MonoidalStructure C } ( β : Braiding m ) ( e : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor ) : Symmetry m := {
  β with 
    symmetry := λ X Y : C.Obj, begin
                                 refine ( cast _ (congr_fun (congr_arg NaturalTransformation.components e) (X, Y)) ),
                                 blast -- TODO rewrite an 'inexact' or 'its' tactic
                               end
}

end tqft.categories.braided_monoidal_category
