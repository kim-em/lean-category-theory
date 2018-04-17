-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.isomorphism

open categories
open categories.functor

namespace categories.isomorphism

universes u

variable {C : Type (u+1)}
variable [category C]
variables {X Y Z : C}

@[simp] lemma Isomorphism.cancel_morphism_left (I : X ≅ Y) (f g : Y ⟶ Z) : I.morphism ≫ f = I.morphism ≫ g ↔ f = g :=
begin
  tidy, 
  have h := congr_arg (λ h, I.inverse ≫ h) a,
  tidy,
end
@[simp] lemma Isomorphism.cancel_morphism_right (I : X ≅ Y) (f g : Z ⟶ X) : f ≫ I.morphism = g ≫ I.morphism ↔ f = g :=
begin
  tidy,
  have h := congr_arg (λ h, h ≫ I.inverse) a,
  tidy,
end
@[simp] lemma Isomorphism.cancel_inverse_left (I : X ≅ Y) (f g : X ⟶ Z) : I.inverse ≫ f = I.inverse ≫ g ↔ f = g :=
begin
  tidy,
  have h := congr_arg (λ h, I.morphism ≫ h) a,
  tidy,
end
@[simp] lemma Isomorphism.cancel_inverse_right (I : X ≅ Y) (f g : Z ⟶ Y) : f ≫ I.inverse = g ≫ I.inverse ↔ f = g :=
begin
  tidy,
  have h := congr_arg (λ h, h ≫ I.morphism) a,
  tidy,
end

end categories.isomorphism