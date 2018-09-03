-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.adjunctions
import category_theory.adjunctions.hom_adjunction

-- FIXME why do we need this here?
@[obviously] meta def obviously_3 := tactic.tidy { tactics := extended_tidy_tactics }

open category_theory

namespace category_theory.adjunctions

universes u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

-- TODO If these are really necessary, move them to category_theory/products.lean
section
variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A] {B : Type u₂} [ℬ : category.{u₂ v₂} B] {C : Type u₃} [𝒞 : category.{u₃ v₃} C] {D : Type u₄} [𝒟 : category.{u₄ v₄} D]
include 𝒜 ℬ 𝒞 𝒟

@[simp,search] lemma prod_obj' (F : A ↝ B) (G : C ↝ D) (a : A) (c : C) : (functor.prod F G).obj (a, c) = (F a, G c) := rfl
@[simp,search] lemma prod_app' {F G : A ↝ B} {H I : C ↝ D} (α : F ⟹ G) (β : H ⟹ I) (a : A) (c : C) : (nat_trans.prod α β).app (a, c) = (α a, β c) := rfl
end

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₁} [𝒟 : category.{u₁ v₁} D]
include 𝒞 𝒟 
variables {L : C ↝ D} {R : D ↝ C} 

@[reducible] private def Adjunction_to_HomAdjunction_morphism (A : L ⊣ R) 
  : ((functor.prod L.op (functor.id D)) ⋙ (functor.hom D)) ⟹ 
                          (functor.prod (functor.id (Cᵒᵖ)) R) ⋙ (functor.hom C) := 
{ app := λ P, 
    -- We need to construct the map from D.Hom (L P.1) P.2 to C.Hom P.1 (R P.2)
    λ f, (A.unit P.1) ≫ (R.map f) }

@[reducible] private def Adjunction_to_HomAdjunction_inverse (A : L ⊣ R) 
  : (functor.prod (functor.id (Cᵒᵖ)) R) ⋙ (functor.hom C) ⟹ 
                          ((functor.prod L.op (functor.id D)) ⋙ (functor.hom D)) :=
{ app := λ P, 
    -- We need to construct the map back to D.Hom (L P.1) P.2 from C.Hom P.1 (R P.2)
    λ f, (L.map f) ≫ (A.counit P.2) }

def Adjunction_to_HomAdjunction (A : L ⊣ R) : hom_adjunction L R := 
{ hom := Adjunction_to_HomAdjunction_morphism A,
  inv := Adjunction_to_HomAdjunction_inverse A }

@[simp,search] lemma mate_of_L (A : hom_adjunction L R) {X Y : C} (f : X ⟶ Y) : (((A.hom) (X, L X)) (𝟙 (L X))) ≫ 
      (R.map (L.map f))
      = ((A.hom) (X, L Y)) (L.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.hom (X, L X) (X, L Y) (𝟙 X, L.map f),
  have q := congr_fun p (L.map (𝟙 X)),
  obviously,
  erw category_theory.functor.map_id at q, -- FIXME why doesn't simp do this
  obviously,
end

@[simp,search] lemma mate_of_L' (A : hom_adjunction L R) {X Y : C} (f : X ⟶ Y) : f ≫ (((A.hom) (Y, L Y)) (𝟙 (L Y)))
      = ((A.hom) (X, L Y)) (L.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.hom (Y, L Y) (X, L Y) (f, 𝟙 (L Y)),
  have q := congr_fun p (L.map (𝟙 Y)),
  obviously,
end

@[simp,search] lemma mate_of_R (A : hom_adjunction L R) {X Y : D} (f : X ⟶ Y) : (L.map (R.map f)) ≫ (((A.inv) (R Y, Y)) (𝟙 (R Y)))
      = ((A.inv) (R X, Y)) (R.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.inv (R Y, Y) (R X, Y) (R.map f, 𝟙 Y),
  have q := congr_fun p (R.map (𝟙 Y)),
  tidy,
end

@[simp,search] lemma mate_of_R' (A : hom_adjunction L R) {X Y : D} (f : X ⟶ Y) : (((A.inv) (R X, X)) (𝟙 (R X))) ≫ f = 
    ((A.inv) (R X, Y)) (R.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.inv (R X, X) (R X, Y) (𝟙 (R X), f),
  have q := congr_fun p (R.map (𝟙 X)),
  obviously,
end

private def counit_from_HomAdjunction (A : hom_adjunction L R) : (R ⋙ L) ⟹ (functor.id _) := 
{ app := λ X : D, (A.inv (R X, X)) (𝟙 (R X)) }

private def unit_from_HomAdjunction (A : hom_adjunction L R) : (functor.id _) ⟹ (L ⋙ R) := 
{ app := λ X : C, (A.hom (X, L X)) (𝟙 (L X)) }

-- PROJECT
-- def HomAdjunction_to_Adjunction {L : C ↝ D} {R : D ↝ C} (A : hom_adjunction L R) : L ⊣ R := 
-- {
--   unit       := unit_from_HomAdjunction A,
--   counit     := counit_from_HomAdjunction A,
--   triangle_1 := begin
--                   tidy, 
--                   -- have p1 := A.witness_2,
--                   -- have p2 := congr_arg NaturalTransformation.components p1,
--                   -- have p3 := congr_fun p2 (((R +> X) : C), L +> (R +> X)),
--                   -- have p4 := congr_fun p3 (𝟙 (R +> X)),
--                   -- tidy,
--                   sorry
--                 end,
--   triangle_2 := sorry
-- }

-- def Adjunctions_agree (L : C ↝ D) (R : D ↝ C) : equiv (L ⊣ R) (hom_adjunction L R) := 
-- { to_fun    := Adjunction_to_HomAdjunction,
--   inv_fun   := HomAdjunction_to_Adjunction,
--   left_inv  := begin sorry end,
--   right_inv := begin
--                  sorry,
--                  -- this is just another lemma about mates; perhaps the same as the one we use above.
--                end }

end category_theory.adjunctions