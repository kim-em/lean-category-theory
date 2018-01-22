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

definition comma_Cone_to_Cone { J C : Category } { F : Functor J C } ( cone : (comma.Cones F).Obj ) : Cone F := 
{
  cone_point    := cone.1,
  cone_maps     := λ j : J.Obj, (cone.2.2).components j,
  commutativity := λ ( j k : J.Obj ) ( f : J.Hom j k ), 
                      begin
                        its eq.symm ((cone.2.2).naturality f),
                      end
}

definition comma_ConeMorphism_to_ConeMorphism { J C : Category } { F : Functor J C } { X Y : (comma.Cones F).Obj } ( f : (comma.Cones F).Hom X Y ) : ConeMorphism (comma_Cone_to_Cone X) (comma_Cone_to_Cone Y) := 
{
  cone_morphism      := f.val.1,
  commutativity := λ j : J.Obj, begin
                                  tidy, -- (This tidy relies on the fact we allow a little bit of looping; no looping actually happens, but our mechanism for detecting looping gets confused.)
                                  let q := congr_arg (λ t : NaturalTransformation _ _, t.components j) f_property,
                                  tidy
                                end
}

definition Cone_to_comma_Cone { J C : Category } { F : Functor J C } ( cone : Cone F ) : (comma.Cones F).Obj := 
⟨ cone.cone_point, ♯, {
    components := λ j, cone.cone_maps j,
    naturality := λ _ _ f, begin
                            its eq.symm (cone.commutativity f) 
                          end
  } ⟩

definition ConeMorphism_to_comma_ConeMorphism { J C : Category } { F : Functor J C } { X Y : Cone F } ( f : ConeMorphism X Y ) : (comma.Cones F).Hom (Cone_to_comma_Cone X) (Cone_to_comma_Cone Y) := 
  ⟨ (f.cone_morphism, ♯), ♯ ⟩

definition comma_Cones_to_Cones { J C : Category } ( F : Functor J C ) : Functor (comma.Cones F) (Cones F) := {
    onObjects     := comma_Cone_to_Cone,
    onMorphisms   := λ _ _ f, comma_ConeMorphism_to_ConeMorphism f
  }

definition Cones_to_comma_Cones { J C : Category } ( F : Functor J C ) : Functor (Cones F) (comma.Cones F) := {
    onObjects     := Cone_to_comma_Cone,
    onMorphisms   := λ _ _ f, ConeMorphism_to_comma_ConeMorphism f
  }

local attribute [applicable] Category.identity

-- PROJECT
-- definition Cones_agree { J C : Category } ( F : Functor J C ) : Equivalence (comma.Cones F) (Cones F) := {
--   functor := comma_Cones_to_Cones F,
--   inverse := Cones_to_comma_Cones F,
--   isomorphism_1 := ♯,
--   isomorphism_2 := ♯
-- }

end categories.universal