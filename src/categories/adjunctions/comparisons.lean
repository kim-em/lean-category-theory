-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.adjunctions
import categories.adjunctions.hom_adjunction

open category_theory

namespace category_theory.adjunctions

universes u

variable {C : Type (u+1)}
variable [large_category C]
variable {D : Type (u+1)}
variable [large_category D]
variables {L : C ↝ D} {R : D ↝ C} 

@[reducible] private definition Adjunction_to_HomAdjunction_morphism (A : L ⊣ R) 
  : ((functor.prod L.opposite (functor.id D)) ⋙ (hom_pairing D)) ⟹ 
                          (functor.prod (functor.id (Cᵒᵖ)) R) ⋙ (hom_pairing C) := 
{ app := λ P, 
    -- We need to construct the map from D.Hom (L P.1) P.2 to C.Hom P.1 (R P.2)
    λ f, (A.unit P.1) ≫ (R.map f) }

@[reducible] private definition Adjunction_to_HomAdjunction_inverse (A : L ⊣ R) 
  : (functor.prod (functor.id (Cᵒᵖ)) R) ⋙ (hom_pairing C) ⟹ 
                          ((functor.prod L.opposite (functor.id D)) ⋙ (hom_pairing D)) :=
{ app := λ P, 
    -- We need to construct the map back to D.Hom (L P.1) P.2 from C.Hom P.1 (R P.2)
    λ f, (L.map f) ≫ (A.counit P.2) }

definition Adjunction_to_HomAdjunction (A : L ⊣ R) : HomAdjunction L R := 
{ map := Adjunction_to_HomAdjunction_morphism A,
  inv := Adjunction_to_HomAdjunction_inverse A }

local attribute [tidy] dsimp_all'

@[simp,ematch] lemma mate_of_L (A : HomAdjunction L R) {X Y : C} (f : X ⟶ Y) : (((A.map) (X, L X)) (𝟙 (L X))) ≫ 
      (R.map (L.map f))
      = ((A.map) (X, L Y)) (L.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.map (X, L X) (X, L Y) (𝟙 X, L.map f),
  have q := congr_fun p (L.map (𝟙 X)),
  tidy,
end

@[simp,ematch] lemma mate_of_L' (A : HomAdjunction L R) {X Y : C} (f : X ⟶ Y) : f ≫ (((A.map) (Y, L Y)) (𝟙 (L Y)))
      = ((A.map) (X, L Y)) (L.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.map (Y, L Y) (X, L Y) (f, 𝟙 (L Y)),
  have q := congr_fun p (L.map (𝟙 Y)),
  tidy,
end

@[simp,ematch] lemma mate_of_R (A : HomAdjunction L R) {X Y : D} (f : X ⟶ Y) : (L.map (R.map f)) ≫ (((A.inv) (R Y, Y)) (𝟙 (R Y)))
      = ((A.inv) (R X, Y)) (R.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.inv (R Y, Y) (R X, Y) (R.map f, 𝟙 Y),
  have q := congr_fun p (R.map (𝟙 Y)),
  tidy,
end

@[simp,ematch] lemma mate_of_R' (A : HomAdjunction L R) {X Y : D} (f : X ⟶ Y) : (((A.inv) (R X, X)) (𝟙 (R X))) ≫ f = 
    ((A.inv) (R X, Y)) (R.map f) :=
begin
  have p := @nat_trans.naturality _ _ _ _ _ _ A.inv (R X, X) (R X, Y) (𝟙 (R X), f),
  have q := congr_fun p (R.map (𝟙 X)),
  tidy,
end

private definition counit_from_HomAdjunction (A : HomAdjunction L R) : (R ⋙ L) ⟹ (functor.id _) := 
{ app := λ X : D, (A.inv (R X, X)) (𝟙 (R X)) }

private definition unit_from_HomAdjunction (A : HomAdjunction L R) : (functor.id _) ⟹ (L ⋙ R) := 
{ app := λ X : C, (A.map (X, L X)) (𝟙 (L X)) }

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