-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import .limits
import .comparisons

open category_theory

universes u v

namespace category_theory.universal

variables {C : Type u} [𝒞 : category.{u v} C] [has_binary_products.{u v} C]
include 𝒞

def prod.of_components {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : P ⟶ (prod Q R) :=
let i := (((prod.universal_property Q R).comparison P).inv) in i (f, g)

def prod.map {P Q R S : C} (f : P ⟶ Q) (g : R ⟶ S) : (prod P R) ⟶ (prod Q S) :=
prod.of_components (prod.π₁ P R ≫ f) (prod.π₂ P R ≫ g)

@[simp,ematch] lemma prod.of_components_π₁ {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : prod.of_components f g ≫ prod.π₁ Q R = f := sorry
@[simp,ematch] lemma prod.of_components_π₂ {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : prod.of_components f g ≫ prod.π₂ Q R = g := sorry

def binary_product.braiding (P Q : C) : prod P Q ≅ prod Q P :=
{ hom := prod.of_components (prod.π₂ _ _) (prod.π₁ _ _),
  inv := prod.of_components (prod.π₂ _ _) (prod.π₁ _ _) }

def binary_product.symmetry (P Q : C) : (binary_product.braiding P Q).hom ≫ (binary_product.braiding Q P).hom = 𝟙 _ :=
begin
  dunfold binary_product.braiding,
  obviously,
end

def binary_product.associativity (P Q R : C) : (prod (prod P Q) R) ≅ (prod P (prod Q R)) :=
{ hom := prod.of_components (prod.π₁ _ _ ≫ prod.π₁ _ _) (prod.of_components (prod.π₁ _ _ ≫ prod.π₂ _ _) (prod.π₂ _ _)),
  inv := prod.of_components (prod.of_components (prod.π₁ _ _) (prod.π₂ _ _ ≫ prod.π₁ _ _)) (prod.π₂ _ _ ≫ prod.π₂ _ _) }

-- TODO verify the pentagon?

end category_theory.universal