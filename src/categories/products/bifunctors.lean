-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

universes u₁ u₂ u₃
variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]
variable {E : Type (u₃+1)}
variable [category E]

@[simp] lemma Bifunctor_identities (F : (C × D) ↝ E) (X : C) (Y : D)
  : @Functor.onMorphisms _ _ _ _ F (X, Y) (X, Y) (𝟙 X, 𝟙 Y) = 𝟙 (F (X, Y))
  := F.identities (X, Y)

@[simp] lemma Bifunctor_left_identity (F : (C × D) ↝ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
  : @Functor.onMorphisms _ _ _ _ F (W, X) (W, Z) (𝟙 W, f ≫ g) =
      (@Functor.onMorphisms _ _ _ _ F (W, X) (W, Y) (𝟙 W, f)) ≫ (@Functor.onMorphisms _ _ _ _ F (W, Y) (W, Z) (𝟙 W, g)) :=
begin
  have p := @Functor.functoriality _ _ _ _ F (W, X) (W, Y) (W, Z) (𝟙 W, f) (𝟙 W, g),
  tidy
end

@[simp] lemma Bifunctor_right_identity (F : (C × D) ↝ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z)
  : @Functor.onMorphisms _ _ _ _ F (X, W) (Z, W) (f ≫ g, 𝟙 W) =
      (@Functor.onMorphisms _ _ _ _ F (X, W) (Y, W) (f, 𝟙 W)) ≫ (@Functor.onMorphisms _ _ _ _ F (Y, W) (Z, W) (g, 𝟙 W)) :=
begin
  have p := @Functor.functoriality _ _ _ _ F (X, W) (Y, W) (Z, W) (f, 𝟙 W) (g, 𝟙 W),
  tidy
end

@[simp] lemma Bifunctor_diagonal_identities_1 (F : (C × D) ↝ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y')
  : (@Functor.onMorphisms _ _ _ _ F (X, Y) (X, Y') (𝟙 X, g)) ≫ (@Functor.onMorphisms _ _ _ _ F (X, Y') (X', Y') (f, 𝟙 Y')) =
   @Functor.onMorphisms _ _ _ _ F (X, Y) (X', Y') (f, g) :=
begin
  have p := eq.symm (@Functor.functoriality _ _ _ _ F (X, Y) (X, Y') (X', Y') (𝟙 X, g) (f, 𝟙 Y')),
  tidy,
end

@[simp] lemma Bifunctor_diagonal_identities_2 (F : (C × D) ↝ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y')
  : (@Functor.onMorphisms _ _ _ _ F (X, Y) (X', Y) (f, 𝟙 Y)) ≫ (@Functor.onMorphisms _ _ _ _ F (X', Y) (X', Y') (𝟙 X', g)) =
   @Functor.onMorphisms _ _ _ _ F (X, Y) (X', Y') (f, g) :=
begin
  have p := eq.symm (@Functor.functoriality _ _ _ _ F (X, Y) (X', Y) (X', Y') (f, 𝟙 Y) (𝟙 X', g)),
  tidy,
end

end categories.products
