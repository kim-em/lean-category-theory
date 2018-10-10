-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Mario Carneiro, Reid Barton

import category_theory.examples.topological_spaces
import category_theory.functor_category
import category_theory.whiskering
import category_theory.natural_isomorphism

universes u v u₂ v₂

open category_theory
open category_theory.examples

namespace category_theory.presheaves

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

structure Presheaf :=
(X : Top.{v})
(𝒪 : (open_set X) ⥤ C)

instance : has_coe_to_sort (Presheaf.{u v} C) :=
{ S := Type v, coe := λ F, F.X.α }

variables {C}

instance Presheaf_topological_space (F : Presheaf.{u v} C) : topological_space F := F.X.str

structure Presheaf_hom (F G : Presheaf.{u v} C) :=
(f : F.X ⟶ G.X)
(c : G.𝒪 ⟹ ((open_set.map f) ⋙ F.𝒪))

@[extensionality] lemma ext {F G : Presheaf.{u v} C} (α β : Presheaf_hom F G)
  (w : α.f = β.f) (h : α.c ⊟ (whisker_right (open_set.map_iso _ _ w).hom F.𝒪) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp at w,
  subst w,
  congr,
  ext,
  have h' := congr_fun (congr_arg nat_trans.app h) X,
  dsimp at h',
  dsimp [open_set.map_iso, whisker_right, whiskering_on_right, nat_iso.of_components, nat_trans.hcomp] at h',
  simp at h',
  dsimp at h',
  rw category.comp_id at h',
  exact h'
end.

namespace Presheaf_hom
def id (F : Presheaf.{u v} C) : Presheaf_hom F F :=
{ f := 𝟙 F.X,
  c := ((functor.id_comp _).inv) ⊟ (whisker_right (open_set.map_id _).inv _) }

def comp {F G H : Presheaf.{u v} C} (α : Presheaf_hom F G) (β : Presheaf_hom G H) : Presheaf_hom F H :=
{ f := α.f ≫ β.f,
  c := β.c ⊟ (whisker_left (open_set.map β.f) α.c) }

/- I tried to break out the axioms for `category (Presheaf C)` below as lemmas here,
   but mysteriously `ext` (nor `apply ext`) doesn't work here! -/
-- lemma comp_id {F G : Presheaf.{u v} C} (α : Presheaf_hom F G) : @comp C _ _ _ _ α (id G) = α :=
-- begin
--   -- ext1, -- why is this failing here, but okay below?!
--   sorry
-- end.
-- lemma id_comp {F G : Presheaf.{u v} C} (α : Presheaf_hom F G) : comp (id F) α = α :=
-- sorry
-- lemma assoc {F G H K : Presheaf.{u v} C} (α : Presheaf_hom F G) (β : Presheaf_hom G H) (γ : Presheaf_hom H K) :
-- comp (comp α β) γ = comp α (comp β γ) := sorry

end Presheaf_hom

variables (C)

instance category_of_presheaves : category (Presheaf.{u v} C) :=
{ hom := Presheaf_hom,
  id := Presheaf_hom.id,
  comp := @Presheaf_hom.comp C _,
  comp_id' := λ X Y f,
  begin
    ext1,
    -- Check the comorphisms
    ext1, -- compare natural transformations componentwise
    dsimp [Presheaf_hom.id, Presheaf_hom.comp],
    dsimp [whisker_right, whiskering_on_right, whisker_left, whiskering_on_left],
    simp,
    erw [category_theory.functor.map_id],
    simp,
    cases X_1, -- Why do we need to do cases before we can finish??!
    simp,
    refl,
    -- Check the functions
    dsimp [Presheaf_hom.id, Presheaf_hom.comp],
    simp,
  end,
  id_comp' := λ X Y f,
  begin
    ext1,
    -- Check the comorphisms
    ext1, -- compare natural transformations componentwise
    dsimp [Presheaf_hom.id, Presheaf_hom.comp],
    dsimp [whisker_right, whiskering_on_right, whisker_left, whiskering_on_left],
    simp,
    erw [category_theory.functor.map_id, category.comp_id, category.comp_id],
    -- Check the functions
    dsimp [Presheaf_hom.id, Presheaf_hom.comp],
    simp,
  end,
  assoc' := λ W X Y Z f g h,
  begin
    ext1,
    swap,
    -- Check the functions
    { dsimp [Presheaf_hom.comp],
      simp only [category.assoc, eq_self_iff_true], },
    -- Check the comorphisms
    { ext1,
      dsimp only [Presheaf_hom.comp,
             whisker_right, whiskering_on_right, whisker_left, whiskering_on_left,
             open_set.map_iso, nat_iso.of_components],
      dsimp, -- This is really slow.
      simp only [category.assoc, category_theory.functor.map_id, category.comp_id],
      erw [category_theory.functor.map_id],
      erw [category_theory.functor.map_id],
      erw [category.comp_id],
      erw [category.comp_id],
      erw [category.id_comp] },
  end }.

namespace Presheaf_hom
@[simp] lemma id_f (F : Presheaf.{u v} C) : ((𝟙 F) : F ⟶ F).f = 𝟙 F.X := rfl
@[simp] lemma id_c (F : Presheaf.{u v} C) : ((𝟙 F) : F ⟶ F).c = (((functor.id_comp _).inv) ⊟ (whisker_right (open_set.map_id _).inv _)) := rfl
@[simp] lemma comp_f {F G H : Presheaf.{u v} C} (α : F ⟶ G) (β : G ⟶ H) : (α ≫ β).f = α.f ≫ β.f := rfl
@[simp] lemma comp_c {F G H : Presheaf.{u v} C} (α : F ⟶ G) (β : G ⟶ H) : (α ≫ β).c = (β.c ⊟ (whisker_left (open_set.map β.f) α.c)) := rfl
end Presheaf_hom

end category_theory.presheaves
