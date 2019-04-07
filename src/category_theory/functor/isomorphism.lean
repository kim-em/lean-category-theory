-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.fully_faithful

open category_theory

namespace category_theory

universes v₁ v₂ u₁ u₂

variables {C : Type u₁} [𝓒 : category.{v₁} C] {D : Type u₂} [𝓓 : category.{v₂} D]
include 𝓒 𝓓

class reflects_isos (F : C ⥤ D) :=
(reflects : Π {X Y : C} (f : X ⟶ Y) (w : is_iso (F.map f)), is_iso f)

instance (F : C ⥤ D) [fully_faithful F] : reflects_isos F :=
{ reflects := λ X Y f,
  by introI w; exact
  { inv := F.preimage (inv (F.map f)),
    hom_inv_id' := begin apply F.injectivity, simp, end,
    inv_hom_id' := begin apply F.injectivity, simp, end }}

-- TODO define reflects_epis, reflects_monos, and deduce these from faithful

end category_theory