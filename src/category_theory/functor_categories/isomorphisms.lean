-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.isomorphism
import category_theory.whiskering

open category_theory

namespace category_theory.functor

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A]
variables {B : Type u₂} [ℬ : category.{u₂ v₂} B]
include 𝒜 ℬ

def left_unitor (F : A ⥤ B) : ((functor.id _) ⋙ F) ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

def right_unitor (F : A ⥤ B) : (F ⋙ (functor.id _)) ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

variables {C : Type u₃} [𝒞 : category.{u₃ v₃} C]
variables {D : Type u₄} [𝒟 : category.{u₄ v₄} D]
include 𝒞 𝒟

def associator (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : ((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H)) :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

omit 𝒟

lemma triangle (F : A ⥤ B) (G : B ⥤ C) :
  (associator F (functor.id B) G).hom ⊟ (whisker_left F (left_unitor G).hom) =
    (whisker_right (right_unitor F).hom G) :=
begin
  ext1,
  dsimp [associator, left_unitor, right_unitor],
  simp
end

variables {E : Type u₅} [ℰ : category.{u₅ v₅} E]
include 𝒟 ℰ

variables (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)

lemma pentagon :
  (whisker_right (associator F G H).hom K) ⊟ (associator F (G ⋙ H) K).hom ⊟ (whisker_left F (associator G H K).hom) =
    ((associator (F ⋙ G) H K).hom ⊟ (associator F G (H ⋙ K)).hom) :=
begin
  ext1,
  dsimp [associator],
  simp,
end

end category_theory.functor
