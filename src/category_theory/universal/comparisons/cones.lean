-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.equivalence
import category_theory.universal.comma_categories
import category_theory.universal

open category_theory
open category_theory.universal
open category_theory.comma

namespace category_theory.universal

universes u v u₁ v₁ u₂ v₂ 
variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞 

@[simp] lemma comma.Cone.commutativity (F : J ↝ C) (X : C) (cone : ((DiagonalFunctor J C) X) ⟶ ((ObjectAsFunctor.{(max u v) v} F).obj punit.star)) {j k : J} (f : j ⟶ k) : cone j ≫ (F.map f) = cone k := 
by obviously

variable {F : J ↝ C}

def comma_Cone_to_Cone (cone : (comma.Cone F)) : Cone F := 
{ cone_point    := cone.1.1,
  cone_maps     := λ j : J, (cone.2) j }

@[simp] lemma comma_Cone_to_Cone_cone_maps  (cone : (comma.Cone F)) (j : J) : (comma_Cone_to_Cone cone).cone_maps j = (cone.2) j := rfl

-- @[simp] lemma refold_nat_trans_coe {A : Type u₁} [category.{u₁ v₁} A] {B : Type u₂} [category.{u₂ v₂} B] {F G : A ↝ B} (α : F ⟹ G) (X : A) : α.app X = α X := rfl

section -- PROJECT improve automation here
def comma_ConeMorphism_to_ConeMorphism {X Y : (comma.Cone F)} (f : comma.comma_morphism X Y) : (comma_Cone_to_Cone X) ⟶ (comma_Cone_to_Cone Y) := 
{ cone_morphism := f.left,
  commutativity := λ j : J, begin                    
                              -- let q := congr_arg nat_trans.app f.condition_lemma,
                              -- let q' := congr_fun q j,
                              -- We need to refold the coercions.!
                              -- cases f,
                              -- obviously,
                              sorry -- FIXME
                            end }
end

def Cone_to_comma_Cone (cone : Cone F) : comma.Cone F := 
⟨ (cone.cone_point, by obviously), { app := λ j, cone.cone_maps j } ⟩

def ConeMorphism_to_comma_ConeMorphism {X Y : Cone F} (f : ConeMorphism X Y) : (Cone_to_comma_Cone X) ⟶ (Cone_to_comma_Cone Y) := 
{ left := f.cone_morphism, 
  right := by obviously }

def comma_Cones_to_Cones (F : J ↝ C) : (comma.Cone F) ↝ (Cone F) := 
{ obj := comma_Cone_to_Cone,
  map' := λ X Y f, comma_ConeMorphism_to_ConeMorphism f }

def Cones_to_comma_Cones (F : J ↝ C) : (Cone F) ↝ (comma.Cone F) := 
{ obj := Cone_to_comma_Cone,
  map' := λ X Y f, ConeMorphism_to_comma_ConeMorphism f }

local attribute [back] category.id
local attribute [tidy] dsimp_all' -- TODO get rid of this
def Cones_agree (F : J ↝ C) : Equivalence (comma.Cone F) (Cone F) := 
{ functor := comma_Cones_to_Cones F,
  inverse := Cones_to_comma_Cones F }

end category_theory.universal