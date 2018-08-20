import .yoneda

def coyoneda : (Cᵒᵖ) ↝ (C ↝ (Type v₁)) := 
{ obj := λ X,      { obj := λ Y, @category.hom C _ X Y,
                     map' := λ Y Y' f g, g ≫ f },
  map' := λ X X' f, { app := λ Y g, f ≫ g } }

@[simp] lemma coyoneda_obj_obj (X Y : C) : ((coyoneda C) X) Y = (X ⟶ Y) := rfl
@[simp] lemma coyoneda_obj_map (X : C) {Y Y' : C} (f : Y ⟶ Y') : ((coyoneda C) X).map f = λ g, g ≫ f := rfl
@[simp] lemma coyoneda_map_app {X X' : C} (f : X ⟶ X') (Y : C) : ((coyoneda C).map f) Y = λ g, f ≫ g := rfl

