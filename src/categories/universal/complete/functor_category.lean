-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .lemmas.cones_in_functor_categories

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.isomorphism
open categories.initial

namespace categories.universal

universes j u₁ u₂
section
variable {J : Type (j+1)}
variable [category J]
variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

@[reducible] private definition evaluate_Functor_to_FunctorCategory (F : Functor J (Functor C D)) (c : C) : Functor J D := {
  onObjects     := λ j, (F j) c,
  onMorphisms   := λ _ _ f, (F &> f).components c
}

@[reducible] private definition evaluate_Functor_to_FunctorCategory_on_Morphism (F : Functor J (Functor C D)) {c c' : C} (f : Hom c c')
  : NaturalTransformation (evaluate_Functor_to_FunctorCategory F c) (evaluate_Functor_to_FunctorCategory F c') := {
    components := λ j, (F j) &> f
 }

-- PROJECT do this properly, as
-- private definition Switch_Curry : Functor (Functor J (Functor C D)) (Functor C (Functor J D)) := 
end

section
variable {J : Type (u₁+1)}
variable [category J]
variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₁+2)}
variable [category D]

private definition LimitObject_in_FunctorCategory [cmp : Complete D] (F : Functor J (Functor C D)) : Cone F := {     
  cone_point    := {
    onObjects     := λ c, functorial_Limit.onObjects (evaluate_Functor_to_FunctorCategory F c), -- TODO why doesn't the coercion work here?
    onMorphisms   := λ _ _ f, functorial_Limit &> (evaluate_Functor_to_FunctorCategory_on_Morphism F f),
 },
  cone_maps     := λ j, {
    components := λ c, (limitCone (evaluate_Functor_to_FunctorCategory F c)).terminal_object.cone_maps j,
 },
}

-- This would be a bit dangerous, but we just use it in the next construction.
@[applicable] lemma cone_morphism_comparison
(F : Functor J (Functor C D))
(X : C)
(j : J)
(Y Z : Cone F)
(φ ψ : ConeMorphism Y Z)
(f : Hom ((Z.cone_point) X) ((F j) X))
(w : f = ((Z.cone_maps j).components X))
 : ((φ.cone_morphism).components X) ≫ f = ((ψ.cone_morphism).components X) ≫ f := 
begin
  rewrite w,
  simp,
end


-- needed for the proof of naturality below
local attribute [reducible] universal.lemmas.limit_functoriality.morphism_to_terminal_object_cone_point

private definition morphism_to_LimitObject_in_FunctorCategory [cmp : Complete D] {F : Functor J (Functor C D)} (Y : Cone F) : ConeMorphism Y (LimitObject_in_FunctorCategory F) := {
      cone_morphism := {
        components := begin
                         tidy,  -- this will use morphism_to_terminal_object_cone_point
                         exact (Y.cone_maps j).components X, 
                         exact congr_fun (congr_arg (NaturalTransformation.components) (Y.commutativity f)) X,  
                       end
     }
   }

instance Limits_in_FunctorCategory [cmp : Complete D] : Complete (Functor C D) := {
  limitCone := λ J _ F, 
  begin
  resetI, -- FIXME why do we need this?
  exact {
    terminal_object                            := LimitObject_in_FunctorCategory F,
    morphism_to_terminal_object_from           := morphism_to_LimitObject_in_FunctorCategory
 }
 end
}

end
end categories.universal