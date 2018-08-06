-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.adjunctions
import categories.adjunctions.hom_adjunction

open category_theory
open category_theory.types

namespace category_theory.adjunctions

universes u

variable {C : Type (u+1)}
variable [large_category C]
variable {D : Type (u+1)}
variable [large_category D]
variables {L : C ↝ D} {R : D ↝ C} 

@[reducible] private definition Adjunction_to_HomAdjunction_morphism (A : L ⊣ R) 
  : ((OppositeFunctor L × Functor.id D) ⋙ (HomPairing D)) ⟹ 
                          ((Functor.id (Cᵒᵖ) × R) ⋙ (HomPairing C)) := 
{ components := λ P, 
    -- We need to construct the map from D.Hom (L P.1) P.2 to C.Hom P.1 (R P.2)
    λ f, (A.unit.components P.1) ≫ (R &> f) }

@[reducible] private definition Adjunction_to_HomAdjunction_inverse (A : L ⊣ R) 
  : ((Functor.id (Cᵒᵖ) × R) ⋙ (HomPairing C)) ⟹ 
                          ((OppositeFunctor L × Functor.id D) ⋙ (HomPairing D)) :=
{ components := λ P, 
    -- We need to construct the map back to D.Hom (L P.1) P.2 from C.Hom P.1 (R P.2)
    λ f, (L &> f) ≫ (A.counit.components P.2) }

definition Adjunction_to_HomAdjunction (A : L ⊣ R) : HomAdjunction L R := 
{ morphism  := Adjunction_to_HomAdjunction_morphism A,
  inverse   := Adjunction_to_HomAdjunction_inverse A }

local attribute [tidy] dsimp_all'

@[simp] lemma mate_of_L (A : HomAdjunction L R) {X Y : C} (f : X ⟶ Y) : (((A.morphism).components (X, L +> X)) (𝟙 (L +> X))) ≫ 
      (R &> (L &> f))
      = ((A.morphism).components (X, L +> Y)) (L &> f) :=
begin
  have p := @NaturalTransformation.naturality _ _ _ _ _ _ A.morphism (X, L +> X) (X, L +> Y) (𝟙 X, L &> f),
  have q := congr_fun p (L &> (𝟙 X)),
  tidy,
end

@[simp] lemma mate_of_L' (A : HomAdjunction L R) {X Y : C} (f : X ⟶ Y) : f ≫ (((A.morphism).components (Y, L +> Y)) (𝟙 (L +> Y)))
      = ((A.morphism).components (X, L +> Y)) (L &> f) :=
begin
  have p := @NaturalTransformation.naturality _ _ _ _ _ _ A.morphism (Y, L +> Y) (X, L +> Y) (f, 𝟙 (L +> Y)),
  have q := congr_fun p (L &> (𝟙 Y)),
  tidy,
end

@[simp] lemma mate_of_R (A : HomAdjunction L R) {X Y : D} (f : X ⟶ Y) : (L &> (R &> f)) ≫ (((A.inverse).components (R.onObjects Y, Y)) (𝟙 (R +> Y)))
      = ((A.inverse).components (R.onObjects X, Y)) (R &> f) :=
begin
  have p := @NaturalTransformation.naturality _ _ _ _ _ _ A.inverse (R.onObjects Y, Y) (R.onObjects X, Y) (R &> f, 𝟙 Y),
  have q := congr_fun p (R &> (𝟙 Y)),
  tidy,
end

@[simp] lemma mate_of_R' (A : HomAdjunction L R) {X Y : D} (f : X ⟶ Y) : (((A.inverse).components (R.onObjects X, X)) (𝟙 (R +> X))) ≫ f = 
    ((A.inverse).components (R.onObjects X, Y)) (R &> f) :=
begin
  have p := @NaturalTransformation.naturality _ _ _ _ _ _ A.inverse (R.onObjects X, X) (R.onObjects X, Y) (𝟙 (R.onObjects X), f),
  have q := congr_fun p (R &> (𝟙 X)),
  tidy,
end

private definition counit_from_HomAdjunction (A : HomAdjunction L R) : (R ⋙ L) ⟹ 1 := {
    components := λ X : D, (A.inverse.components (R.onObjects X, X)) (𝟙 (R +> X)),
 }

private definition unit_from_HomAdjunction (A : HomAdjunction L R) : 1 ⟹ (L ⋙ R) := {
    components := λ X : C, (A.morphism.components (X, L +> X)) (𝟙 (L +> X)),
 }

-- PROJECT
-- definition HomAdjunction_to_Adjunction {L : C ↝ D} {R : D ↝ C} (A : HomAdjunction L R) : L ⊣ R := 
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

-- definition Adjunctions_agree (L : C ↝ D) (R : D ↝ C) : equiv (L ⊣ R) (HomAdjunction L R) := 
-- { to_fun    := Adjunction_to_HomAdjunction,
--   inv_fun   := HomAdjunction_to_Adjunction,
--   left_inv  := begin sorry end,
--   right_inv := begin
--                  sorry,
--                  -- this is just another lemma about mates; perhaps the same as the one we use above.
--                end }

end category_theory.adjunctions