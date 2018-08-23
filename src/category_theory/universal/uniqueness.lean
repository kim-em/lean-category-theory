import .limits

universes u v

open category_theory

namespace category_theory.universal

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

local attribute [back] homs_to_binary_product_eq homs_to_equalizer_eq homs_to_pullback_eq homs_to_limit_eq

def terminals_iso (A B : terminal_object.{u v} C) : A.X ≅ B.X :=
{ hom := B.h.lift A.X,
  inv := A.h.lift B.X }

def binary_products_iso {Y Z : C} (A B : span.{u v} Y Z) (A_w : is_binary_product A) (B_w : is_binary_product B) : A.X ≅ B.X :=
{ hom := B_w.lift A,
  inv := A_w.lift B }

def equalizers_iso {Y Z : C} {f g : Y ⟶ Z} (A B : equalizer.{u v} f g) : A.X ≅ B.X :=
{ hom := B.h.lift A.t,
  inv := A.h.lift B.t,
  hom_inv_id := begin apply homs_to_equalizer_eq; simp * end,
  inv_hom_id := begin apply homs_to_equalizer_eq; simp * end }

def pullbacks_iso {Y₁ Y₂ Z : C} {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} (A B : pullback.{u v} r₁ r₂) : A.X ≅ B.X :=
{ hom := B.h.lift A.t,
  inv := A.h.lift B.t,
  hom_inv_id := begin apply homs_to_pullback_eq; simp * end,
  inv_hom_id := begin apply homs_to_pullback_eq; simp * end }

variables {J : Type v} [𝒥 : small_category J]
include 𝒥

def limits_iso {F : J ↝  C} (A B : limit.{u v} F) : A.X ≅ B.X :=
{ hom := B.h.lift A.t,
  inv := A.h.lift B.t,
  hom_inv_id := begin apply homs_to_limit_eq; simp * end,
  inv_hom_id := begin apply homs_to_limit_eq; simp * end }

end category_theory.universal
