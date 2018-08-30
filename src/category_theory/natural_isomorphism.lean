-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.isomorphism
import category_theory.functor_category
import category_theory.tactics.obviously

namespace category_theory

universes u₁ u₂ v₁ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

def nat_iso (F G : C ↝ D) := F ≅ G

infix ` ⇔ `:10 := nat_iso -- type as \<=>

namespace nat_iso

def app {F G : C ↝ D} (α : F ⇔ G) (X : C) : F X ≅ G X :=
{ hom := α.hom X,
  inv := α.inv X,
  hom_inv_id' := begin rw ← functor.category.comp_app, rw iso.hom_inv_id, tidy, end,
  inv_hom_id' := begin rw ← functor.category.comp_app, rw iso.inv_hom_id, tidy, end }

instance {F G : C ↝ D} : has_coe_to_fun (F ⇔ G) :=
{ F   := λ α, Π X : C, (F X) ≅ (G X),
  coe := λ α, α.app }

@[simp,ematch] lemma comp_app {F G H : C ↝ D} (α : F ⇔ G) (β : G ⇔ H) (X : C) : 
  ((α ≪≫ β) : F ⟹ H) X = α X ≪≫ β X := rfl


variables {F G H : C ↝ D}

section 
variable (α : F ⇔ G)
@[simp,ematch] lemma hom_inv_id (X : C) : ((α X) : F X ⟶ G X) ≫ ((α.symm X) : G X ⟶ F X) = 𝟙 (F X) := by obviously 
@[simp,ematch] lemma inv_hom_id (X : C) : ((α.symm X) : G X ⟶ F X) ≫ ((α X) : F X ⟶ G X) = 𝟙 (G X) := by obviously

@[ematch] lemma {u1 v1 u2 v2} naturality_1 {X Y : C} (f : X ⟶ Y) : (α.symm X) ≫ (F.map f) ≫ ((α Y) : F Y ⟶ G Y) = G.map f := by obviously
@[ematch] lemma {u1 v1 u2 v2} naturality_2 {X Y : C} (f : X ⟶ Y) : ((α X) : F X ⟶ G X) ≫ (G.map f) ≫ (α.symm Y) = F.map f := by obviously
end

def from_components
  (app : ∀ X : C, (F X) ≅ (G X))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (app Y).hom = (app X).hom ≫ (G.map f)) : F ⇔ G :=
{ hom  := { app := λ X, (app X).hom, },
  inv  := { app := λ X, (app X).inv,
            naturality' := λ X Y f, begin 
                                      let p := congr_arg (λ f, (app X).inv ≫ (f ≫ (app Y).inv)) (eq.symm (naturality f)),
                                      obviously,
                                    end } }

def vcomp (α : F ⇔ G) (β : G ⇔ H) : F ⇔ H := iso.trans α β

instance hom.app.is_iso (α : F ⇔ G) (X : C) : is_iso (α.hom X) := 
{ inv := α.inv X }
instance inv.app.is_iso   (α : F ⇔ G) (X : C) : is_iso (α.inv X) := 
{ inv := α.hom X }

@[reducible] def symm (α : F ⇔ G) : G ⇔ F := 
{ hom := α.inv,
  inv := α.hom }

end nat_iso

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
