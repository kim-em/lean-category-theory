-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.products.bifunctors
import categories.equivalence

namespace category_theory

universes u₁ u₂ v₂ 

variables {C : Type u₁} [small_category C] {D : Type u₁} [small_category D] {E : Type u₂} [ℰ : category.{u₂ v₂} E]
include ℰ

def uncurry : (C ↝ (D ↝ E)) ↝ ((C × D) ↝ E) := 
{ obj := λ F, { obj := λ X, (F X.1) X.2,
                map := λ X Y f, ((F.map f.1) X.2) ≫ ((F Y.1).map f.2) },
  map := λ F G T, { app := λ X, (T X.1) X.2 } }

def curry : ((C × D) ↝ E) ↝ (C ↝ (D ↝ E)) := 
{ obj := λ F, { obj := λ X, { obj := λ Y, F (X, Y),
                              map := λ Y Y' g, F.map (𝟙 X, g) },
                map := λ X X' f, { app := λ Y, F.map (f, 𝟙 Y) } },
  map := λ F G T, { app := λ X, { app := λ Y, T (X, Y) } } }

local attribute [back] category.id -- this is usually a bad idea, but just what we needed here

def currying : Equivalence (C ↝ (D ↝ E)) ((C × D) ↝ E) := 
{ functor := uncurry,
  inverse := curry }

end category_theory