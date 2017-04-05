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
    apply NaturalTransformations_componentwise_equal,
    intros,
    dsimp,
    unfold_unfoldable_hypotheses,
    induction X with X1 X2,
    unfold squared_Braiding._proof_1,
    -- At this point we have an unpleasant goal involving many eq.rec's, that I can't seem to do anything with.
      -- C : Category,
      -- m : MonoidalStructure C,
      -- β : braided_monoidal_category.Symmetry m,
      -- X1 X2 : C.Obj
      -- ⊢ (eq.rec
      -- (vertical_composition_of_NaturalTransformations ((β.braiding).morphism)
      --     (whisker_on_left (SwitchProductCategory C C) ((β.braiding).morphism)))
      -- (eq.rec
      --     (eq.rec
      --       (eq.rec (eq.refl (NaturalTransformation (m.tensor) (m.tensor)))
      --           (eq.symm (FunctorComposition.left_identity (C × C) C (m.tensor))))
      --       (eq.symm (switch_twice_is_the_identity C C)))
      --     (FunctorComposition.associativity (SwitchProductCategory C C) (SwitchProductCategory C C)
      --       (m.tensor)))).components
      -- (X1, X2) = (IdentityNaturalTransformation (m.tensor)).components (X1, X2)

    admit   
  end

end tqft.categories.braided_monoidal_category
