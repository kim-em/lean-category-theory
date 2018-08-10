-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.natural_transformation
import categories.isomorphism
import categories.opposites
import categories.equivalence
import categories.products.switch
import categories.types
import categories.functor_categories.evaluation
import categories.universe_lifting
import tactic.interactive
import categories.tactics.obviously

open category_theory

namespace category_theory.yoneda

universes u₁ v₁ u₂

section
variables (C : Type u₁) [category.{u₁ v₁} C]

-- We need to help typeclass inference with some awkward universe levels here.
instance instance_1 : category (((Cᵒᵖ) ↝ Type v₁) × (Cᵒᵖ)) := category_theory.prod.category.{(max u₁ (v₁+1)) (max u₁ v₁) u₁ v₁} (Cᵒᵖ ↝ Type v₁) (Cᵒᵖ)
instance instance_2 : category ((Cᵒᵖ) × ((Cᵒᵖ) ↝ Type v₁)) := category_theory.prod.category.{u₁ v₁ (max u₁ (v₁+1)) (max u₁ v₁)} (Cᵒᵖ) (Cᵒᵖ ↝ Type v₁) 

definition yoneda_evaluation : (((Cᵒᵖ) ↝ (Type v₁)) × (Cᵒᵖ)) ↝ (Type (max u₁ v₁)) 
  := (evaluation (Cᵒᵖ) (Type v₁)) ⋙ type_lift.{v₁ u₁}

-- FIXME hmmm.
open tactic.interactive
meta def unfold_coes' := `[unfold_coes]
local attribute [tidy] unfold_coes'

definition yoneda : C ↝ ((Cᵒᵖ) ↝ (Type v₁)) := 
{ obj := λ X, 
    { obj := λ Y, @category.Hom C _ Y X,
      map := λ Y Y' f g, f ≫ g },
  map := λ X X' f, 
    { app := λ Y g, g ≫ f } }

-- FIXME typeclass resolution needs some help.
definition yoneda_pairing : (((Cᵒᵖ) ↝ (Type v₁)) × (Cᵒᵖ)) ↝ (Type (max u₁ v₁)) := 
let F := (ProductCategory.switch ((Cᵒᵖ) ↝ (Type v₁)) (Cᵒᵖ)) in
let G := (functor.prod ((yoneda C).opposite) (functor.id ((Cᵒᵖ) ↝ (Type v₁)))) in
let H := (hom_pairing ((Cᵒᵖ) ↝ (Type v₁))) in
  (F ⋙ G ⋙ H)      


definition coyoneda (C : Type u₁) [category.{u₁ v₁} C] : (Cᵒᵖ) ↝ (C ↝ (Type v₁)) := 
{ obj := λ X, 
   { obj := λ Y, @category.Hom C _ X Y,
     map := λ Y Y' f g, g ≫ f },
  map := λ X X' f,
    { app := λ Y g, f ≫ g } }
end

section
variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞

class Representable (F : C ↝ (Type v₁)) := 
(c : C)
(Φ : F ⇔ ((coyoneda C) c))

end

@[simp] private lemma YonedaLemma_aux_1 {C : Type u₁} [category.{u₁ v₁} C] {X Y : C} (f : X ⟶ Y) {F G : (Cᵒᵖ) ↝ (Type v₁)} (τ : F ⟹ G) (Z : F Y) :
     (G.map f) ((τ Y) Z) = (τ X) ((F.map f) Z) := eq.symm (congr_fun (τ.naturality f) Z)

local attribute [tidy] dsimp_all'

set_option pp.universes true

-- FIXME
def YonedaLemma (C : Type u₁) [category.{u₁ v₁} C] : (yoneda_pairing C) ⇔ (yoneda_evaluation C) := 
{ map := { app := λ F x, ulift.up ((x.app F.2) (𝟙 F.2)), naturality := by sorry },
  inv := { app := λ F x, { app := λ X a, (F.1.map a) x.down }, naturality := by sorry },
  map_inv_id := sorry }.

def YonedaFull (C : Type u₁) [category.{u₁ v₁} C] : Full (yoneda C) := 
{ preimage := λ X Y f, (f X) (𝟙 X),
  witness := λ X Y f, begin tidy, have p := congr_fun (f.naturality x) (𝟙 X), tidy, end } -- PROJECT a pure rewriting proof?

def YonedaFaithful (C : Type u₁) [category.{u₁ v₁} C]  : Faithful (yoneda C) := {
    injectivity := λ X Y f g w, begin 
                                  -- PROJECT automation
                                  dsimp_all',
                                  have p := congr_arg nat_trans.app w, 
                                  have p' := congr_fun p X, 
                                  have p'' := congr_fun p' (𝟙 X),
                                  tidy,
                                end
}

end category_theory.yoneda