-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import categories.isomorphism
import categories.functor_categories

namespace category_theory

universes u₁ u₂ v₁ v₂

variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

definition NaturalIsomorphism (F G : C ↝ D) := F ≅ G

infix ` ⇔ `:10 := NaturalIsomorphism -- type as \<=>

namespace NaturalIsomorphism

-- It's a pity we need to separately define this coercion.
-- Ideally the coercion from Isomorphism along .morphism would just apply here.
-- Somehow we want the definition above to be more transparent?
instance coercion_to_NaturalTransformation (F G : C ↝ D) : has_coe (F ⇔ G) (F ⟹ G) :=
  {coe := λ α, iso.map α}

variables {F G H : C ↝ D}

section 
variable (α : F ⇔ G)
@[simp,ematch] lemma map_inv_id (X : C) : (α.map X) ≫ (α.inv X) = 𝟙 (F X) := by obviously'
@[simp,ematch] lemma inv_map_id (X : C) : (α.inv X) ≫ (α.map X) = 𝟙 (G X) := by obviously'
@[simp,ematch] lemma map_inv_id_assoc {X : C} {Z : D} (f : (F X) ⟶ Z) : (α.map X) ≫ (α.inv X) ≫ f = f := by obviously'
@[simp,ematch] lemma inv_map_id_assoc {X : C} {Z : D} (f : (G X) ⟶ Z) : (α.inv X) ≫ (α.map X) ≫ f = f := by obviously'

@[ematch] lemma {u1 v1 u2 v2} naturality_1 {X Y : C} (f : X ⟶ Y) : (α.inv X) ≫ (F.map f) ≫ (α.map Y) = G.map f := by obviously
@[ematch] lemma {u1 v1 u2 v2} naturality_2 {X Y : C} (f : X ⟶ Y) : (α.map X) ≫ (G.map f) ≫ (α.inv Y) = F.map f := by obviously
end

definition from_components
  (app : ∀ X : C, (F X) ≅ (G X))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (app Y).map = (app X).map ≫ (G.map f)) : NaturalIsomorphism F G :=
{ map  := { app := λ X, (app X).map, },
  inv  := { app := λ X, (app X).inv,
            naturality := λ X Y f, begin 
                                    let p := congr_arg (λ f, (app X).inv ≫ (f ≫ (app Y).inv)) (eq.symm (naturality f)),
                                    tidy,
                                   end } }

definition vertical_composition (α : F ⇔ G) (β : G ⇔ H) : F ⇔ H := iso.trans α β

-- TODO why this?
attribute [reducible] NaturalIsomorphism

@[reducible] definition components (α : F ⇔ G) (X : C) : (F X) ≅ (G X) := 
{ map := α.map X,
  inv := α.inv X }

instance morphisms.components.is_Isomorphism (α : F ⇔ G) (X : C) : is_iso (α.map X) := 
{ inv := α.inv X }
instance inverse.components.is_Isomorphism   (α : F ⇔ G) (X : C) : is_iso (α.inv X) := 
{ inv := α.map X }

@[reducible] definition reverse (α : F ⇔ G) : G ⇔ F := 
{ map := α.inv,
  inv := α.map }

end NaturalIsomorphism

open nat_trans

variables {F G : C ↝ D}

definition is_NaturalIsomorphism  (α : F ⟹ G) := @is_iso (C ↝ D) (category_theory.functor_category C D) F G α
attribute [class] is_NaturalIsomorphism

namespace is_NaturalIsomorphism
-- TODO [is_NaturalIsomorphism α]
@[simp,ematch] lemma componentwise_witness_1 (α : F ⟹ G) (w : is_NaturalIsomorphism α) (X : C) : (α X) ≫ (w.inv.app X) = 𝟙 (F X)
   := sorry
@[simp,ematch] lemma componentwise_witness_2 (α : F ⟹ G) (w : is_NaturalIsomorphism α) (X : C) : (w.inv.app X) ≫ (α X) = 𝟙 (G X)
   := sorry

instance (F : C ↝ D) : is_NaturalIsomorphism (𝟙 F) := 
{ inv := 𝟙 F }

end is_NaturalIsomorphism

namespace NaturalIsomorphism

instance morphism.is_NaturalIsomorphism {F G : C ↝ D} (α : F ⇔ G) : is_NaturalIsomorphism (α.map) := 
{ inv := α.inv }
instance inverse.is_NaturalIsomorphism  {F G : C ↝ D} (α : F ⇔ G) : is_NaturalIsomorphism (α.inv) := 
{ inv := α.map }

end NaturalIsomorphism

end category_theory
