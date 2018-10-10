-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.embedding
import category_theory.tactics.obviously

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃

structure equivalence (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] :=
(functor : C ⥤ D)
(inverse : D ⥤ C)
(fun_inv_id' : (functor ⋙ inverse) ≅ (category_theory.functor.id C) . obviously)
(inv_fun_id' : (inverse ⋙ functor) ≅ (category_theory.functor.id D) . obviously)

restate_axiom equivalence.fun_inv_id'
restate_axiom equivalence.inv_fun_id'

infixr ` ≌ `:10  := equivalence

namespace equivalence

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

def refl : C ≌ C :=
{ functor := functor.id C,
  inverse := functor.id C }

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

def symm (e : C ≌ D) : D ≌ C :=
{ functor := e.inverse,
  inverse := e.functor,
  fun_inv_id' := e.inv_fun_id,
  inv_fun_id' := e.fun_inv_id }

@[simp,search] lemma fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = (e.inv_fun_id.hom X) ≫ f ≫ (e.inv_fun_id.inv Y) := by obviously
@[simp,search] lemma inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = (e.fun_inv_id.hom X) ≫ f ≫ (e.fun_inv_id.inv Y) := by obviously

variables {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include ℰ

attribute [trans] category.comp

def effe_id (e : C ≌ D) (f : D ≌ E) (X : C) : (e.inverse) ((f.inverse) ((f.functor) ((e.functor) X))) ⟶ X :=
calc
  _ ⟶ (e.inverse) ((e.functor) X) : e.inverse.map (f.fun_inv_id.hom.app _)
... ⟶ X                           : e.fun_inv_id.hom.app _
def id_effe (e : C ≌ D) (f : D ≌ E) (X : C) : (functor.id C) X ⟶ ((e.functor ⋙ f.functor) ⋙ f.inverse ⋙ e.inverse) X :=
calc
  X ⟶ (e.functor ⋙ e.inverse) X : e.fun_inv_id.inv.app _
... ⟶ _                           : e.inverse.map (f.fun_inv_id.inv.app _)
def feef_id (e : C ≌ D) (f : D ≌ E) (X : E) : (f.functor) ((e.functor) ((e.inverse) ((f.inverse) X))) ⟶ X :=
calc
  _ ⟶ (f.functor) ((f.inverse) X) : f.functor.map (e.inv_fun_id.hom.app _)
... ⟶ X                           : f.inv_fun_id.hom.app _
def id_feef (e : C ≌ D) (f : D ≌ E) (X : E) : X ⟶ ((f.inverse ⋙ e.inverse) ⋙ e.functor ⋙ f.functor) X :=
calc
  X ⟶ (f.inverse ⋙ f.functor) X : f.inv_fun_id.inv.app _
... ⟶ _                           : f.functor.map (e.inv_fun_id.inv.app _)

set_option trace.tidy true

-- def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E :=
-- { functor := e.functor ⋙ f.functor,
--   inverse := f.inverse ⋙ e.inverse,
--   fun_inv_id' :=
--   { hom := { app := λ X, effe_id e f X, naturality' :=
--       begin
--         dsimp [effe_id],
--         intros,
--         rw ← category.assoc,
--         rw ← functor.map_comp,
--         rw nat_trans.app_eq_coe,
--         erw nat_trans.naturality ((fun_inv_id f).hom), -- work out why this is so difficult: we must be missing something
--         sorry
--       end
--       /-begin tidy, rewrite_search_using [`search] end-/ }, -- These fail, exceeding max iterations.
--     inv := { app := λ X, id_effe e f X, naturality' := sorry },
--     hom_inv_id' := sorry, -- These seem to work: 13 step rewrites!
--     inv_hom_id' := sorry },
--   inv_fun_id' :=
--   { hom := { app := λ X, feef_id e f X, naturality' := sorry },
--     inv := { app := λ X, id_feef e f X, naturality' := sorry },
--     hom_inv_id' := sorry,
--     inv_hom_id' := sorry },
--  }

end equivalence

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

section
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

class is_equivalence (F : C ⥤ D) :=
(inverse        : D ⥤ C)
(fun_inv_id' : (F ⋙ inverse) ≅ (functor.id C) . obviously)
(inv_fun_id' : (inverse ⋙ F) ≅ (functor.id D) . obviously)

restate_axiom is_equivalence.fun_inv_id'
restate_axiom is_equivalence.inv_fun_id'
end

namespace functor
instance is_equivalence_refl : is_equivalence (functor.id C) :=
{ inverse := functor.id C }
end functor

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

namespace functor
def inv (F : C ⥤ D) [is_equivalence F] : D ⥤ C :=
is_equivalence.inverse F

instance is_equivalence_symm (F : C ⥤ D) [is_equivalence F] : is_equivalence (F.inv) :=
{ inverse := F,
  fun_inv_id' := is_equivalence.inv_fun_id F,
  inv_fun_id' := is_equivalence.fun_inv_id F }

def fun_inv_id (F : C ⥤ D) [is_equivalence F] : (F ⋙ F.inv) ≅ functor.id C :=
is_equivalence.fun_inv_id F

def inv_fun_id (F : C ⥤ D) [is_equivalence F] : (F.inv ⋙ F) ≅ functor.id D :=
is_equivalence.inv_fun_id F

def as_equivalence (F : C ⥤ D) [is_equivalence F] : C ≌ D :=
{ functor := F,
  inverse := is_equivalence.inverse F,
  fun_inv_id' := is_equivalence.fun_inv_id F,
  inv_fun_id' := is_equivalence.inv_fun_id F }

variables {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include ℰ

-- instance is_equivalence_trans (F : C ⥤ D) (G : D ⥤ E) [is_equivalence F] [is_equivalence G] :
--   is_equivalence (F ⋙ G) := sorry

end functor

namespace is_equivalence
instance is_equivalence_functor (e : C ≌ D) : is_equivalence e.functor :=
{ inverse := e.inverse,
  fun_inv_id' := e.fun_inv_id,
  inv_fun_id' := e.inv_fun_id }
instance is_equivalence_inverse (e : C ≌ D) : is_equivalence e.inverse :=
{ inverse := e.functor,
  fun_inv_id' := e.inv_fun_id,
  inv_fun_id' := e.fun_inv_id }

@[simp,search] lemma fun_inv_map (F : C ⥤ D) [is_equivalence F] (X Y : D) (f : X ⟶ Y) : F.map (F.inv.map f) = (F.inv_fun_id.hom.app X) ≫ f ≫ (F.inv_fun_id.inv.app Y) := by obviously
@[simp,search] lemma inv_fun_map (F : C ⥤ D) [is_equivalence F] (X Y : C) (f : X ⟶ Y) : F.inv.map (F.map f) = (F.fun_inv_id.hom.app X) ≫ f ≫ (F.fun_inv_id.inv.app Y) := by obviously

end is_equivalence

class ess_surj (F : C ⥤ D) :=
(obj_preimage (d : D) : C)
(iso' (d : D) : F (obj_preimage d) ≅ d . obviously)

restate_axiom ess_surj.iso'

namespace functor
def obj_preimage (F : C ⥤ D) [ess_surj F] (d : D) : C := ess_surj.obj_preimage.{u₁ v₁ u₂ v₂} F d
def fun_obj_preimage_iso (F : C ⥤ D) [ess_surj F] (d : D) : F (F.obj_preimage d) ≅ d := ess_surj.iso F d
end functor


end category_theory