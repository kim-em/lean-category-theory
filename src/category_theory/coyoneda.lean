import .yoneda

universes u₁ v₁ 

open category_theory

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

def coyoneda : (Cᵒᵖ) ⥤ (C ⥤ (Type v₁)) := 
{ obj := λ X : C, { obj := λ Y, X ⟶ Y,
                map' := λ Y Y' f g, g ≫ f },
  map' := λ X X' f, { app := λ Y g, f ≫ g } }

@[simp] lemma coyoneda_obj_obj (X Y : C) : ((coyoneda C) X) Y = (X ⟶ Y) := rfl
@[simp] lemma coyoneda_obj_map (X : C) {Y Y' : C} (f : Y ⟶ Y') : ((coyoneda C) X).map f = λ g, g ≫ f := rfl
@[simp] lemma coyoneda_map_app {X X' : C} (f : X ⟶ X') (Y : C) : ((coyoneda C).map f) Y = λ g, f ≫ g := rfl

-- Does anyone need the coyoneda lemma as well?
