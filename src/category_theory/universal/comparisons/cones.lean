-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.equivalence
import category_theory.limits.cones
import category_theory.universal.comma_categories
import category_theory.limits.obviously

open category_theory
open category_theory.comma

namespace category_theory.limits

universes u v u₁ v₁ u₂ v₂

variables {J : Type v} [small_category J] {C : Type u} [𝒞 : category.{u v} C]
variable {F : J ⥤ C}

section
include 𝒞

@[simp] lemma comma.Cone.commutativity (F : J ⥤ C) (X : C) (c : ((DiagonalFunctor J C) X) ⟶ ((ObjectAsFunctor.{(max u v) v} F).obj punit.star)) {j k : J} (f : j ⟶ k) : c j ≫ (F.map f) = c k :=
by obviously

def comma_Cone_to_Cone (c : (comma.Cone F)) : cone F :=
{ X := c.1.1,
  π := λ j : J, (c.2) j }

@[simp] lemma comma_Cone_to_Cone_cone_maps  (c : (comma.Cone F)) (j : J) : (comma_Cone_to_Cone c).π j = (c.2) j := rfl

def comma_ConeMorphism_to_ConeMorphism {X Y : (comma.Cone F)} (f : comma.comma_morphism X Y) : (comma_Cone_to_Cone X) ⟶ (comma_Cone_to_Cone Y) :=
{ hom := f.left, w' :=
begin
intro j,
have h := f.condition,
simp at h,
dsimp [comma_Cone_to_Cone],
sorry,
end }

def Cone_to_comma_Cone (c : cone F) : comma.Cone F :=
⟨ (c.X, by obviously), { app := λ j, c.π j } ⟩

def ConeMorphism_to_comma_ConeMorphism {X Y : cone F} (f : cone_morphism X Y) : (Cone_to_comma_Cone X) ⟶ (Cone_to_comma_Cone Y) :=
{ left := f.hom,
  right := by obviously }

def comma_Cones_to_Cones (F : J ⥤ C) : (comma.Cone F) ⥤ (cone F) :=
{ obj := comma_Cone_to_Cone,
  map' := λ X Y f, comma_ConeMorphism_to_ConeMorphism f }

def Cones_to_comma_Cones (F : J ⥤ C) : (cone F) ⥤ (comma.Cone F) :=
{ obj := Cone_to_comma_Cone,
  map' := λ X Y f, ConeMorphism_to_comma_ConeMorphism f }.

end /- end `include 𝒞` -/

local attribute [back] category.id

private meta def dsimp' := `[dsimp at * {unfold_reducible := tt, md := semireducible}]
local attribute [tidy] dsimp'

include 𝒞

def Cones_agree (F : J ⥤ C) : equivalence (comma.Cone F) (cone F) :=
{ functor := comma_Cones_to_Cones F,
  inverse := Cones_to_comma_Cones F }

end category_theory.limits