-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.products
import categories.tactics.obviously

open category_theory

namespace category_theory.ProductCategory

universes u₁ v₁ u₂ v₂
variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
variable {D : Type u₁}
variable [𝒟 : category.{u₁ v₁} D]
variable {E : Type u₂}
variable [ℰ : category.{u₂ v₂} E]
include 𝒞 𝒟 ℰ

@[simp] lemma Bifunctor_identities (F : (C × D) ↝ E) (X : C) (Y : D)
  : @category_theory.functor.map _ _ _ _ F (X, Y) (X, Y) (𝟙 X, 𝟙 Y) = 𝟙 (F (X, Y))
  := F.map_id (X, Y)

@[simp] lemma Bifunctor_left_identity (F : (C × D) ↝ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
  : @category_theory.functor.map _ _ _ _ F (W, X) (W, Z) (𝟙 W, f ≫ g) =
      (@category_theory.functor.map _ _ _ _ F (W, X) (W, Y) (𝟙 W, f)) ≫ (@category_theory.functor.map _ _ _ _ F (W, Y) (W, Z) (𝟙 W, g)) := by obviously

@[simp] lemma Bifunctor_right_identity (F : (C × D) ↝ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z)
  : @category_theory.functor.map _ _ _ _ F (X, W) (Z, W) (f ≫ g, 𝟙 W) =
      (@category_theory.functor.map _ _ _ _ F (X, W) (Y, W) (f, 𝟙 W)) ≫ (@category_theory.functor.map _ _ _ _ F (Y, W) (Z, W) (g, 𝟙 W)) := by obviously

@[simp] lemma Bifunctor_diagonal_identities_1 (F : (C × D) ↝ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y')
  : (@category_theory.functor.map _ _ _ _ F (X, Y) (X, Y') (𝟙 X, g)) ≫ (@category_theory.functor.map _ _ _ _ F (X, Y') (X', Y') (f, 𝟙 Y')) =
   @category_theory.functor.map _ _ _ _ F (X, Y) (X', Y') (f, g) := by obviously

@[simp] lemma Bifunctor_diagonal_identities_2 (F : (C × D) ↝ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y')
  : (@category_theory.functor.map _ _ _ _ F (X, Y) (X', Y) (f, 𝟙 Y)) ≫ (@category_theory.functor.map _ _ _ _ F (X', Y) (X', Y') (𝟙 X', g)) =
   @category_theory.functor.map _ _ _ _ F (X, Y) (X', Y') (f, g) := by obviously

end category_theory.ProductCategory
