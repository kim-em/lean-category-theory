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

/-
Dear Jeremy,

Thanks. While that succeeds with my toy example, I can't help but feel that it misses the point! (Which, admittedly, was perhaps not very clear in my toy example.) I have examples where more "essential" work happens in the rewriting lemma. It may take me some time to come up with a good intermediate complexity example.

For now, let me try to describe one situation it arises. In monoidal_categories/lemma/symmetry_in_terms_of_natural_transformations.lean, I study braidings and symmetries on monoidal categories. For the purposes here, a "tensor product" is a functor `C \times C` to `C`, where `C` is a category and "\times" is the obvious notion of cartesian product of categories. A "commutor" for a tensor product `m` is a natural transformation from `m` to the functor where first we switch the factors of `C \times C`, and then use `m`. In terms of components, a commutor `c` is a collection of morphisms `c_{X,Y} : X \otimes Y \to Y \otimes X`. Now, there are two ways to say a commutor is "symmetric". First, we can say it in terms of components: if we compose c_{X,Y} with c_{Y,X}, we should get the identity. Second we can express this as an equation between natural transformations. The goal in this particular file is just to show that these are equivalent, and in particular to prove this equation between natural transformations from the statement in components.

The subtlety is that the commutor is not something we can literally "square", as it is a transformation between `m` and `\sigma \circ m` (where \sigma denotes switching the factors of `C \times C`). So instead we
compose the commutor `c` with the commutor 'whiskered' by `\sigma` (this is a transformation from `\sigma \circ m` to `\sigma \circ \sigma \circ m`), obtaining a transformation from `m` to `\sigma \circ \sigma \circ m`.
We now use associativitiy of functor composition, and the lemma that `\sigma \circ \sigma` is the identity functor on `C \times C`, to see that we've obtained a natural transformation from `m` to `m`. The part of the
construction is the definition `squared_Braiding`. You can see it uses the idiom of "saying what the answer is, and then showing that it was actually the correct type", using `refine ( cast _ square )`.

Now in the lemma `symmetry_in_terms_of_natural_transformations` we have to show that this natural transformation really is the identity natural transformation. This should be easy after we write everything in terms of components,
but it's not 
-/

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
