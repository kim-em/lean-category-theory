-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...isomorphism
import ...natural_transformation
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
variable {J : Type j}
variable [category J]
variable {C : Type u}
variable [category C]
variable {F : Functor J C}

definition comma_Cone_to_Cone (cone : (comma.Cone F)) : Cone F := 
{
  cone_point    := cone.1.1,
  cone_maps     := λ j : J, (cone.2).components j,
  commutativity := λ (j k : J) (f : Hom j k), 
                      begin
                        its eq.symm ((cone.2).naturality f),
                      end
}

definition comma_ConeMorphism_to_ConeMorphism {X Y : (comma.Cone F)} (f : Hom X Y) : ConeMorphism (comma_Cone_to_Cone X) (comma_Cone_to_Cone Y) := 
{
  cone_morphism      := f.left,
  commutativity := λ j : J, begin
                                  tidy, -- (This tidy relies on the fact we allow a little bit of looping; no looping actually happens, but our mechanism for detecting looping gets confused.)
                                  let q := congr_arg (λ t : NaturalTransformation _ _, t.components j) f.condition,
                                  tidy
                                end
}

definition Cone_to_comma_Cone (cone : Cone F) : comma.Cone F := 
⟨ (cone.cone_point, ♯), {
    components := λ j, cone.cone_maps j,
    naturality := λ _ _ f, begin
                            its eq.symm (cone.commutativity f) 
                          end
 } ⟩

definition ConeMorphism_to_comma_ConeMorphism {X Y : Cone F} (f : ConeMorphism X Y) : Hom (Cone_to_comma_Cone X) (Cone_to_comma_Cone Y) := 
  { left := f.cone_morphism, right := ♯ }

definition comma_Cones_to_Cones (F : Functor J C) : Functor (comma.Cone F) (Cone F) := {
    onObjects     := comma_Cone_to_Cone,
    onMorphisms   := λ _ _ f, comma_ConeMorphism_to_ConeMorphism f
 }

definition Cones_to_comma_Cones (F : Functor J C) : Functor (Cone F) (comma.Cone F) := {
    onObjects     := Cone_to_comma_Cone,
    onMorphisms   := λ _ _ f, ConeMorphism_to_comma_ConeMorphism f
 }

local attribute [applicable] category.identity

definition Cones_agree (F : Functor J C) : Equivalence (comma.Cone F) (Cone F) := {
  functor := comma_Cones_to_Cones F,
  inverse := Cones_to_comma_Cones F,
  isomorphism_1 := ♯,
  isomorphism_2 := ♯
}

end categories.universal