-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

namespace tqft.categories.braided_monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.monoidal_category

universe variables u v

/-
-- I don't really understand why the universe annotations are needed in Braiding and in squaredBraiding.
-- My guess is that it is related to
-- https://groups.google.com/d/msg/lean-user/3qzchWkut0g/0QR6_cS8AgAJ
-/

@[reducible] definition Braiding(C : MonoidalCategory.{u v}) := 
  NaturalIsomorphism (C^.tensor) (FunctorComposition (SwitchProductCategory C C) C^.tensor)

structure BraidedMonoidalCategory
  extends parent: MonoidalCategory.{u v} :=
  (braiding: Braiding parent)
-- TODO hexagon, in components, and a theorem it holds as a natural transformation

instance BraidedMonoidalCategory_coercion_to_MonoidalCategory : has_coe BraidedMonoidalCategory MonoidalCategory := ⟨BraidedMonoidalCategory.to_MonoidalCategory⟩

structure SymmetricMonoidalCategory
  extends parent: BraidedMonoidalCategory.{u v} :=
  (symmetry: Π X Y : Obj, compose (braiding^.morphism^.components ⟨X, Y⟩) (braiding^.morphism^.components ⟨Y, X⟩) = identity (tensor^.onObjects ⟨X, Y⟩) )

attribute [ematch,simp] SymmetricMonoidalCategory.symmetry

instance SymmetricMonoidalCategory_coercion_to_BraidedMonoidalCategory : has_coe SymmetricMonoidalCategory BraidedMonoidalCategory := ⟨SymmetricMonoidalCategory.to_BraidedMonoidalCategory⟩

end tqft.categories.braided_monoidal_category