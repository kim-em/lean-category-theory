-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category
import categories.tactics.obviously

namespace category_theory

universes u v

variable {C : Type (u+1)}
variables {X Y Z : C}
variable [large_category C]

@[simp] def cancel_left (f g : X ⟶ Y) : (∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) ↔ f = g :=
begin
    split,
    { intro w, convert w (𝟙 Y), tidy },
    { obviously }
end
@[simp] def cancel_right (f g : Y ⟶ Z) : (∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) ↔ f = g :=
begin
    split,
    { intro w, convert w (𝟙 Y), tidy },
    { obviously }
end
@[simp] def identity_if_it_quacks_left (f : X ⟶ X) : (∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) ↔ f = 𝟙 X :=
begin
    split,
    { intro w, convert w (𝟙 X), tidy },
    { obviously }
end
@[simp] def identity_if_it_quacks_right (f : X ⟶ X) : (∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) ↔ f = 𝟙 X :=
begin
    split,
    { intro w, convert w (𝟙 X), tidy },
    { obviously }
end

end category_theory