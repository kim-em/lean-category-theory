import category_theory.limits

universes u v

open category_theory

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section

@[extensionality] lemma homs_to_terminal_ext (X' : C) (X : C) [is_terminal.{u v} X] (f g : X' ⟶ X) : f = g :=
begin
  rw is_terminal.uniq X X' f,
  rw is_terminal.uniq X X' g,
end

def terminals_iso (A B : C) [is_terminal.{u v} A] [is_terminal.{u v} B] : A ≅ B :=
{ hom := is_terminal.lift.{u v} B A,
  inv := is_terminal.lift.{u v} A B }
end

section
def binary_products_iso {Y Z : C} (A B : span.{u v} Y Z) (A_w : is_binary_product A) (B_w : is_binary_product B) : A.X ≅ B.X :=
{ hom := B_w.lift A,
  inv := A_w.lift B,
  hom_inv_id' := sorry, 
  inv_hom_id' := sorry }
end

section
def equalizers_iso {Y Z : C} {f g : Y ⟶ Z} (A B : fork.{u v} f g) (A_w : is_equalizer A) (B_w : is_equalizer B) : A.X ≅ B.X :=
{ hom := B_w.lift A,
  inv := A_w.lift B,
  hom_inv_id' := sorry, 
  inv_hom_id' := sorry }
end

section
def pullbacks_iso {Y₁ Y₂ Z : C} {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} (A B : square.{u v} r₁ r₂) (A_w : is_pullback A) (B_w : is_pullback B): A.X ≅ B.X :=
{ hom := B_w.lift A,
  inv := A_w.lift B,
  hom_inv_id' := sorry, 
  inv_hom_id' := sorry }
end

variables {J : Type v} [𝒥 : small_category J]
include 𝒥

section
-- FIXME this is a horrible formulation
lemma homs_to_limit_ext  {F : J ⥤ C} (c : cone.{u v} F) (B : is_limit c) {X : C} (f g : X ⟶ c.X) (w : ∀ j, f ≫ c.π j = g ≫ c.π j) : f = g :=
begin
  let s : cone F := ⟨ ⟨ X ⟩, λ j, f ≫ c.π j, by obviously ⟩,
  have q := B.uniq s f,
  have p := B.uniq s g,
  rw [q, ←p],
  intros,
  rw ← w j,
  intros,
  refl
end


local attribute [back] homs_to_limit_ext
def limits_iso {F : J ⥤  C} (A B : cone.{u v} F) (A_w : is_limit A) (B_w : is_limit B) : A.X ≅ B.X :=
{ hom := B_w.lift A,
  inv := A_w.lift B }
end

end category_theory.limits
