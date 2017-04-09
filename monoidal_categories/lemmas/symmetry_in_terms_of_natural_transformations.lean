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


-- FIXME We need this lemma for now, because we can't unfold ProductCategory without messing up implicit arguments.
@[simp] lemma {u1 u2 u3 u4} product_identities_1 { C : Category.{u1 u2} } { D : Category.{u3 u4} } { X : C.Obj } { Y : D.Obj } : ((C × D).identity (X, Y)).1 = C.identity X := ♯
@[simp] lemma {u1 u2 u3 u4} product_identities_2 { C : Category.{u1 u2} } { D : Category.{u3 u4} } { X : C.Obj } { Y : D.Obj } : ((C × D).identity (X, Y)).2 = D.identity Y := ♯

lemma {u v} symmetry_in_terms_of_natural_transformations { C : Category.{u v} } { m : MonoidalStructure C } ( β : Symmetry m ) : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor := 
  begin
    apply NaturalTransformations_componentwise_equal,
    intros,
    induction X with X_1 X_2,
    -- unfold_unfoldable, -- FIXME unfold_unfoldable messes up implicit arguments
    -- simp
    unfold squared_Braiding, 
    unfold IdentityNaturalTransformation,
    unfold vertical_composition_of_NaturalTransformations,
    dsimp,
    unfold whisker_on_left,
    unfold whisker_on_right,
    unfold horizontal_composition_of_NaturalTransformations,
    unfold IdentityNaturalTransformation,
    dsimp,
    unfold FunctorComposition,
    unfold SwitchSymmetry,
    unfold FunctorComposition_associator,
    unfold FunctorComposition_left_unitor,
    dsimp,
    unfold SwitchProductCategory,
    dsimp,
    simp,
    unfold eq.mpr,
    unfold eq.mpr._proof_1,
    unfold FunctorComposition_associator._proof_2,
    unfold SwitchSymmetry._proof_1,
    unfold FunctorComposition_left_unitor._proof_1,
    simp
  end

lemma {u v} symmetric_in_terms_of_components { C : Category.{u v} } { m : MonoidalStructure C } ( β : Braiding m ) ( e : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor ) : Symmetry m := {
  β with 
    symmetry := λ X Y : C.Obj, begin
                                 refine ( cast _ (congr_fun (congr_arg NaturalTransformation.components e) (X, Y)) ),
                                 unfold squared_Braiding,
                                 unfold IdentityNaturalTransformation,
                                 unfold vertical_composition_of_NaturalTransformations,
                                 dsimp,
                                 unfold whisker_on_left,
                                 unfold whisker_on_right,
                                 unfold horizontal_composition_of_NaturalTransformations,
                                 unfold IdentityNaturalTransformation,
                                 dsimp,
                                 unfold FunctorComposition,
                                 unfold SwitchSymmetry,
                                 unfold FunctorComposition_associator,
                                 unfold FunctorComposition_left_unitor,
                                 dsimp,
                                 unfold SwitchProductCategory,
                                 dsimp,
                                 simp
                               end
}

end tqft.categories.braided_monoidal_category
