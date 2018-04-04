-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...equivalence
import ..comma_categories
import ..universal

import tidy.its

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.equivalence
open categories.universal

namespace categories.universal

universes u j
variable {J : Type (j+1)}
variable [category J]
variable {C : Type (u+2)}
variable [category C]
variable {F : Functor J C}

definition comma_Cone_to_Cone (cone : (comma.Cone F)) : Cone F := 
{
  cone_point    := cone.1.1,
  cone_maps     := λ j : J, (cone.2).components j,
  commutativity := λ (j k : J) (f : j ⟶ k), 
                      begin
                        -- have p := eq.symm (cone.2.naturality_lemma f), 
                        obviously -- TODO so we can just remove commutativity
                      end
}

definition comma_ConeMorphism_to_ConeMorphism {X Y : (comma.Cone F)} (f : comma.comma_morphism X Y) : (comma_Cone_to_Cone X) ⟶ (comma_Cone_to_Cone Y) := 
{
  cone_morphism := f.left,
  commutativity := λ j : J, begin
                              let q := congr_arg (λ t : NaturalTransformation _ _, t.components j) f.condition,
                              tidy
                            end
}

definition Cone_to_comma_Cone (cone : Cone F) : comma.Cone F := 
⟨ (cone.cone_point, by obviously), {
    components := λ j, cone.cone_maps j,
    naturality := λ _ _ f, begin
                            its eq.symm (cone.commutativity f),
                            tidy,
                          end
 } ⟩

definition ConeMorphism_to_comma_ConeMorphism {X Y : Cone F} (f : ConeMorphism X Y) : (Cone_to_comma_Cone X) ⟶ (Cone_to_comma_Cone Y) := 
  { left := f.cone_morphism, right := by obviously }

definition comma_Cones_to_Cones (F : J ↝ C) : (comma.Cone F) ↝ (Cone F) := {
    onObjects     := comma_Cone_to_Cone,
    onMorphisms   := λ X Y f, comma_ConeMorphism_to_ConeMorphism f,
 }

definition Cones_to_comma_Cones (F : J ↝ C) : (Cone F) ↝ (comma.Cone F) := {
    onObjects     := Cone_to_comma_Cone,
    onMorphisms   := λ X Y f, ConeMorphism_to_comma_ConeMorphism f
 }

local attribute [applicable] category.identity

-- FIXME really slow: need to automatically abstract (propositional?) subgoals
-- definition Cones_agree (F : J ↝ C) : Equivalence (comma.Cone F) (Cone F) := {
--   functor := comma_Cones_to_Cones F,
--   inverse := Cones_to_comma_Cones F,
--   isomorphism_1 := by obviously,
--   isomorphism_2 := by obviously
-- }

end categories.universal