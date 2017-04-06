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

-- universe variables u v

definition {u v} transport {A : Type u} { P : A → Type v} {x y : A} (p : x = y)
(u : P x) : P y :=
by induction p; exact u

definition {u v w} apdt011 {A : Type u} {Z : Type w} {B : A → Type v} (f : Πa, B a → Z) {a a' : A} {b : B a} {b' : B a'} (Ha : a = a') (Hb : transport Ha b = b')
      : f a b = f a' b' :=
by cases Ha; cases Hb; reflexivity

set_option trace.check true

@[reducible] definition {u v} squared_Braiding { C : Category.{u v} } { m : MonoidalStructure C } ( commutor : Commutor m )
  : NaturalTransformation m.tensor m.tensor :=
  begin
    pose square := vertical_composition_of_NaturalTransformations commutor.morphism (whisker_on_left (SwitchProductCategory C C) commutor.morphism),
    -- refine ( cast _ square ),
    refine ( transport _ square ),
    rewrite - FunctorComposition.associativity,
    erewrite switch_twice_is_the_identity,
    rewrite FunctorComposition.left_identity,
  end 

lemma {u v} symmetry_in_terms_of_natural_transformations { C : Category.{u v} } { m : MonoidalStructure C } ( β : Symmetry m ) : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor := 
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

lemma symmetric_in_terms_of_components { C : Category.{u v} } { m : MonoidalStructure C } ( β : Braiding m ) ( e : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor ) : Symmetry m := {
  β with 
    symmetry := λ X Y : C.Obj, begin
                                 refine ( cast _ (congr_fun (congr_arg NaturalTransformation.components e) (X, Y)) ),
                                 unfold_unfoldable,
                                 unfold squared_Braiding._proof_1,
                                 -- Again, we're stuck with eq.rec,

                                 admit
                               end
}

end tqft.categories.braided_monoidal_category
