-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.isomorphism
import category_theory.functor_category
import category_theory.tactics.obviously

namespace category_theory

universes u₁ u₂ v₁ v₂

variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

def NaturalIsomorphism (F G : C ↝ D) := F ≅ G

infix ` ⇔ `:10 := NaturalIsomorphism -- type as \<=>

namespace NaturalIsomorphism

-- It's a pity we need to separately define this coercion.
-- Ideally the coercion from Isomorphism along .morphism would just apply here.
-- Somehow we want the def above to be more transparent?
instance coercion_to_NaturalTransformation (F G : C ↝ D) : has_coe (F ⇔ G) (F ⟹ G) :=
  {coe := λ α, iso.hom α}

variables {F G H : C ↝ D}

section 
variable (α : F ⇔ G)
@[simp,ematch] lemma hom_inv_id (X : C) : (α.hom X) ≫ (α.inv X) = 𝟙 (F X) := by obviously'
@[simp,ematch] lemma inv_hom_id (X : C) : (α.inv X) ≫ (α.hom X) = 𝟙 (G X) := by obviously'
@[simp,ematch] lemma hom_inv_id_assoc {X : C} {Z : D} (f : (F X) ⟶ Z) : (α.hom X) ≫ (α.inv X) ≫ f = f := by obviously'
@[simp,ematch] lemma inv_hom_id_assoc {X : C} {Z : D} (f : (G X) ⟶ Z) : (α.inv X) ≫ (α.hom X) ≫ f = f := by obviously'

@[ematch] lemma {u1 v1 u2 v2} naturality_1 {X Y : C} (f : X ⟶ Y) : (α.inv X) ≫ (F.map f) ≫ (α.hom Y) = G.map f := by obviously
@[ematch] lemma {u1 v1 u2 v2} naturality_2 {X Y : C} (f : X ⟶ Y) : (α.hom X) ≫ (G.map f) ≫ (α.inv Y) = F.map f := by obviously
end

def from_components
  (app : ∀ X : C, (F X) ≅ (G X))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (app Y).hom = (app X).hom ≫ (G.map f)) : NaturalIsomorphism F G :=
{ hom  := { app := λ X, (app X).hom, },
  inv  := { app := λ X, (app X).inv,
            naturality := λ X Y f, begin 
                                    let p := congr_arg (λ f, (app X).inv ≫ (f ≫ (app Y).inv)) (eq.symm (naturality f)),
                                    obviously,
                                   end } }

def vertical_composition (α : F ⇔ G) (β : G ⇔ H) : F ⇔ H := iso.trans α β

-- TODO why this?
attribute [reducible] NaturalIsomorphism

@[reducible] def components (α : F ⇔ G) (X : C) : (F X) ≅ (G X) := 
{ hom := α.hom X,
  inv := α.inv X }

instance hom.app.is_iso (α : F ⇔ G) (X : C) : is_iso (α.hom X) := 
{ inv := α.inv X }
instance inv.app.is_iso   (α : F ⇔ G) (X : C) : is_iso (α.inv X) := 
{ inv := α.hom X }

@[reducible] def symm (α : F ⇔ G) : G ⇔ F := 
{ hom := α.inv,
  inv := α.hom }

end NaturalIsomorphism

open nat_trans

variables {F G : C ↝ D}

def is_nat_iso  (α : F ⟹ G) := @is_iso (C ↝ D) (category_theory.functor.category C D) F G α
attribute [class] is_nat_iso

namespace is_nat_iso
-- TODO [is_nat_iso α]
@[simp,ematch] lemma hom_inv_id_app (α : F ⟹ G) (w : is_nat_iso α) (X : C) : (α X) ≫ (w.inv.app X) = 𝟙 (F X)
   := by obviously
@[simp,ematch] lemma inv_hom_id_app (α : F ⟹ G) (w : is_nat_iso α) (X : C) : (w.inv.app X) ≫ (α X) = 𝟙 (G X)
   := by obviously

instance (F : C ↝ D) : is_nat_iso (𝟙 F) := 
{ inv := 𝟙 F }

end is_nat_iso

namespace nat_iso

instance hom.is_nat_iso {F G : C ↝ D} (α : F ⇔ G) : is_nat_iso (α.hom) := 
{ inv := α.inv }
instance inv.is_nat_iso  {F G : C ↝ D} (α : F ⇔ G) : is_nat_iso (α.inv) := 
{ inv := α.hom }

end nat_iso

end category_theory
