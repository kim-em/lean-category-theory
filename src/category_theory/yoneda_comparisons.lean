import category_theory.yoneda
import category_theory.follow_your_nose

universes u₁ v₁

open category_theory

-- Unimath, Coq
-- https://github.com/UniMath/UniMath/blob/master/UniMath/CategoryTheory/yoneda.v
-- Greg O'Keefe, Isabelle
-- https://www.isa-afp.org/browser_info/current/AFP/Category/document.pdf
-- Alexander Katovsky, Isabelle
-- https://www.isa-afp.org/browser_info/current/AFP/Category2/document.pdf
-- Gross, Chlipala, Spivak, Coq
-- https://arxiv.org/src/1401.7694v2/anc/HoTT/theories/categories/Yoneda.v

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

def yoneda_0 : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁)) := 
{ obj := λ X,
  { obj := λ Y : C, Y ⟶ X,
    map := λ Y Y' f g, f ≫ g,
    map_comp' := begin intros X_1 Y Z f g, ext1, dsimp at *, erw [category.assoc] end,
    map_id' := begin intros X_1, ext1, dsimp at *, erw [category.id_comp] end },
  map := λ X X' f,
    { app := λ Y g, g ≫ f,
      naturality' := begin intros X_1 Y f_1, ext1, dsimp at *, simp at * end },
  map_comp' := begin intros X Y Z f g, ext1, ext1, dsimp at *, simp at * end,
  map_id' := begin intros X, ext1, ext1, dsimp at *, simp at * end }

def yoneda_1 : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁)) := 
{ obj := λ X,
  { obj := λ Y : C, Y ⟶ X,
    map := λ Y Y' f g, f ≫ g,
    map_comp' := begin intros X_1 Y Z f g, ext1, dsimp at *, erw [category.assoc] end,
    map_id' := begin intros X_1, ext1, dsimp at *, erw [category.id_comp] end },
  map := λ X X' f, { app := λ Y g, g ≫ f } }

def yoneda_2 : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁)) := 
{ obj := λ X,
  { obj := λ Y : C, Y ⟶ X,
    map := λ Y Y' f g, f ≫ g },
  map := λ X X' f, { app := λ Y g, g ≫ f } }

def yoneda_3 : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁)) := ƛ X, ƛ Y : C, Y ⟶ X.

def yoneda_lemma' : (yoneda_pairing C) ≅ (yoneda_evaluation C) := 
{ hom := { app := λ F x, ulift.up ((x.app F.1) (𝟙 F.1)) },
  inv := { app := λ F x, { app := λ X a, (F.2.map a) x.down } } }.
