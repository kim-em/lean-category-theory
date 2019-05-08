-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category
import category_theory.tactics.obviously

namespace category_theory

universes v u

variables {C : Sort u} {X Y Z : C} [𝒞 : category.{v} C]
include 𝒞

def eq_of_comp_left_eq {f g : X ⟶ Y} (h : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g :=
by { convert h (𝟙 Y), tidy }
def eq_of_comp_right_eq {f g : Y ⟶ Z} (h : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) : f = g :=
by { convert h (𝟙 Y), tidy }

def eq_of_comp_left_eq' (f g : X ⟶ Y) (w : (λ {Z : C} (h : Y ⟶ Z), f ≫ h) = (λ {Z : C} (h : Y ⟶ Z), g ≫ h)) : f = g :=
eq_of_comp_left_eq (λ Z h, begin
 have p := congr_fun w Z,
 exact congr_fun p h,
end)
def eq_of_comp_right_eq' (f g : Y ⟶ Z) (w : (λ {X : C} (h : X ⟶ Y), h ≫ f) = (λ {X : C} (h : X ⟶ Y), h ≫ g)) : f = g :=
eq_of_comp_right_eq (λ X h, begin
 have p := congr_fun w X,
 have q := congr_fun p h,
 exact q
end)

def id_of_comp_left_id (f : X ⟶ X) (h : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X :=
by { convert h (𝟙 X), tidy }
def id_of_comp_right_id (f : X ⟶ X) (h : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X :=
by { convert h (𝟙 X), tidy }

end category_theory