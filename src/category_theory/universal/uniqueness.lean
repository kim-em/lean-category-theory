import .limits

universes u v

open category_theory

namespace category_theory.universal

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

-- TODO would it be better to prove this once for limits, and then use the fact that the others are special cases?
-- TODO using all these local [back] attributes is gross: can we improve backwards_reasoning so it's safe to mark these as [back] throughout?

section
local attribute [back] homs_to_terminal_ext
def terminals_iso (A B : C) (A_w : is_terminal.{u v} A) (B_w : is_terminal.{u v} B) : A ≅ B :=
{ hom := B_w.lift A,
  inv := A_w.lift B }
end

section
local attribute [back] homs_to_binary_product_ext
def binary_products_iso {Y Z : C} (A B : span.{u v} Y Z) (A_w : is_binary_product A) (B_w : is_binary_product B) : A.X ≅ B.X :=
{ hom := B_w.lift A,
  inv := A_w.lift B }
end

section
local attribute [back] homs_to_equalizer_ext
def equalizers_iso {Y Z : C} {f g : Y ⟶ Z} (A B : equalizer.{u v} f g) : A.X ≅ B.X :=
{ hom := B.h.lift A.t,
  inv := A.h.lift B.t }
end

section
local attribute [back] homs_to_pullback_ext
def pullbacks_iso {Y₁ Y₂ Z : C} {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} (A B : square.{u v} r₁ r₂) (A_w : is_pullback A) (B_w : is_pullback B): A.X ≅ B.X :=
{ hom := B_w.lift A,
  inv := A_w.lift B }
end

variables {J : Type v} [𝒥 : small_category J]
include 𝒥

section
local attribute [back] homs_to_limit_ext
def limits_iso {F : J ↝  C} (A B : cone.{u v} F) (A_w : is_limit A) (B_w : is_limit B) : A.X ≅ B.X :=
{ hom := B_w.lift A,
  inv := A_w.lift B }
end

end category_theory.universal
