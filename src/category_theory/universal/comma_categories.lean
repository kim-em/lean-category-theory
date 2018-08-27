-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor_category
import category_theory.walking
import category_theory.discrete_category
import category_theory.universal.limits
import category_theory.universal.colimits

open category_theory
open category_theory.universal
open category_theory.walking

namespace category_theory.comma

universes j u₁ v₁ u₂ v₂ u₃ v₃

section
variables (J : Type u₁) [𝒥 : category.{u₁ v₁} J] (C : Type u₂) [𝒞 : category.{u₂ v₂} C] 
include 𝒥 𝒞
-- The diagonal functor sends X to the constant functor that sends everything to X.
def DiagonalFunctor : C ↝ (J ↝ C) :=
{ obj := λ X, { obj := λ _, X,
                map' := λ _ _ _, 𝟙 X },
  map' := λ X Y f, { app := λ _, f } }

@[simp] lemma DiagonalFunctor_map_app {X Y : C} (f : X ⟶ Y) (j : J) : ((DiagonalFunctor J C).map f) j = f := rfl
end

def ObjectAsFunctor {C : Type u₃} [category.{u₃ v₃} C] (X : C) : functor.{u₃ v₃ u₃ v₃} punit C := 
{ obj := λ _, X,
  map' := λ _ _ _, 𝟙 X }

@[simp] lemma ObjectAsFunctor_map {C : Type u₃} [category.{u₃ v₃} C] (X : C) (P Q : punit) (h : @category.hom.{u₃ v₃} punit _ P Q) : @category_theory.functor.map _ _ _ _ (ObjectAsFunctor.{u₃ v₃} X) P Q h = 𝟙 X := rfl

section
local attribute [ematch] subtype.property

variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A] {B : Type u₂} [ℬ : category.{u₂ v₂} B] {C : Type u₃} [𝒞 : category.{u₃ v₃} C]
include 𝒜 ℬ 𝒞

def comma (S : A ↝ C) (T : B ↝ C) : Type (max u₁ u₂ v₃) := Σ p : A × B, (S p.1) ⟶ (T p.2)

structure comma_morphism {S : A ↝ C} {T : B ↝ C} (p q : comma S T) : Type (max v₁ v₂):=
(left : p.1.1 ⟶ q.1.1)
(right : p.1.2 ⟶ q.1.2)
(condition : (S.map left) ≫ q.2 = p.2 ≫ (T.map right) . obviously)

restate_axiom comma_morphism.condition
attribute [ematch] comma_morphism.condition_lemma

@[extensionality] lemma comma_morphism_equal
  {S : A ↝ C} {T : B ↝ C} {p q : comma S T} (f g : comma_morphism p q)
  (wl : f.left = g.left) (wr : f.right = g.right) : f = g :=
  begin
    induction f,
    induction g,
    tidy,
  end

instance CommaCategory (S : A ↝ C) (T : B ↝ C) : category.{(max u₁ u₂ v₃) (max v₁ v₂)} (comma S T) :=
{ hom  := λ p q, comma_morphism p q,
  id   := λ p, ⟨ 𝟙 p.1.1, 𝟙 p.1.2, by obviously ⟩,
  comp := λ p q r f g, ⟨ f.left ≫ g.left, f.right ≫ g.right, by obviously ⟩ }

-- cf Leinster Remark 2.3.2
def CommaCategory_left_projection (S : A ↝ C) (T : B ↝ C) : (comma S T) ↝ A := 
{ obj := λ X, X.1.1,
  map' := λ _ _ f, f.left }

def CommaCategory_right_projection (S : A ↝ C) (T : B ↝ C) : (comma S T) ↝ B := 
{ obj := λ X, X.1.2,
  map' := λ _ _ f, f.right }

def CommaCategory_projection_transformation (S : A ↝ C) (T : B ↝ C) : ((CommaCategory_left_projection S T) ⋙ S) ⟹ ((CommaCategory_right_projection S T) ⋙ T) := 
{ app := λ X, X.2 }

-- Notice that if C is large, these are large, and if C is small, these are small.
def SliceCategory   (X : C) : category.{(max u₃ v₃) v₃} (comma (functor.id C) (ObjectAsFunctor X)) := by apply_instance
def CosliceCategory (X : C) : category.{(max u₃ v₃) v₃} (comma (ObjectAsFunctor X) (functor.id C)) := by apply_instance
end

-- In Cones, we have
--   A = C
--   B = .
--   C = FunctorCategory J C
variable {J : Type v₁}
variable [small_category J]
variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞

def Cone   (F : J ↝ C) := 
(comma (DiagonalFunctor.{v₁ v₁ u₁ v₁} J C) (ObjectAsFunctor F))
def Cocone (F : J ↝ C) := 
(comma (ObjectAsFunctor F) (DiagonalFunctor.{v₁ v₁ u₁ v₁} J C)).

@[ematch] lemma Cone.pointwise_condition_lemma {F : J ↝ C} (X Y : Cone F) (f : comma_morphism X Y) (j : J) : f.left ≫ (Y.snd) j = (X.snd) j := 
begin
  have p := f.condition_lemma,
  have p' := congr_arg nat_trans.app p,
  have p'' := congr_fun p' j,
  simp at p'',
  rw nat_trans.refold_coe at p'',
  obviously
end

@[simp] lemma Cone_comma_unit   (F : J ↝ C) (X : Cone F)   : X.1.2 = punit.star := by obviously 
@[simp] lemma Cocone_comma_unit (F : J ↝ C) (X : Cocone F) : X.1.1 = punit.star := by obviously 

instance Cones   (F : J ↝ C) : category (Cone F)   := begin unfold Cone, apply_instance end
instance Cocones (F : J ↝ C) : category (Cocone F) := begin unfold Cocone, apply_instance end

-- def Limit   (F: J ↝ C) := terminal_object (Cone   F)
-- def Colimit (F: J ↝ C) := initial_object  (Cocone F)

-- def BinaryProduct   (α β : C)                  := Limit   (Pair_functor.{u₁ v₁} α β)
-- def BinaryCoproduct (α β : C)                  := Colimit (Pair_functor α β)
-- def Equalizer       {α β : C} (f g : α ⟶ β)  := Limit   (ParallelPair_functor f g)
-- def Coequalizer     {α β : C} (f g : α ⟶ β)  := Colimit (ParallelPair_functor f g)

end category_theory.comma

