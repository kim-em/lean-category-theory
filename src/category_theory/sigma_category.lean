-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.fully_faithful

/- This is exactly analogous to the full_subcategory definition for a subtype, but
for a sigma type instead. -/

namespace category_theory

universes v u w

section
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

instance sigma_category (Z : C → Type w) : category.{v} (Σ X : C, Z X) :=
{ hom  := λ X Y, X.1 ⟶ Y.1,
  id   := λ X, 𝟙 X.1,
  comp := λ _ _ _ f g, f ≫ g }

def sigma_category_embedding (Z : C → Type w) : (Σ X : C, Z X) ⥤ C :=
{ obj := λ X, X.1,
  map := λ _ _ f, f }

instance sigma_category_full     (Z : C → Type w) : full     (sigma_category_embedding Z) := by obviously
instance sigma_category_faithful (Z : C → Type w) : faithful (sigma_category_embedding Z) := by obviously
end

end category_theory