-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .cones
import ..util.finite

open categories
open categories.functor
open categories.isomorphism
open categories.initial
open categories.types
open categories.util.finite

namespace categories.universal

universes u₁ u₂
variables {C : Type (u₁+1)}
variables [category C]
variables {X Y : C}

structure Equalizer (f g : X ⟶ Y) :=
  (equalizer     : C)
  (inclusion     : equalizer ⟶ X)
  (map           : ∀ {Z : C} (k : Z ⟶ X) (w : k ≫ f = k ≫ g), Z ⟶ equalizer)
  (witness       : inclusion ≫ f = inclusion ≫ g . obviously)
  (factorisation : ∀ {Z : C} (k : Z ⟶ X) (w : k ≫ f = k ≫ g), (map k w) ≫ inclusion = k . obviously)
  (uniqueness    : ∀ {Z : C} (a b : Z ⟶ equalizer) (witness : a ≫ inclusion = b ≫ inclusion), a = b . obviously)

make_lemma Equalizer.witness
make_lemma Equalizer.factorisation
make_lemma Equalizer.uniqueness
attribute [simp,search] Equalizer.factorisation_lemma
attribute [applicable] Equalizer.inclusion Equalizer.map
attribute [applicable] Equalizer.uniqueness_lemma

-- Or should we write out yet another structure, and prove it agrees with the equalizer?
definition Kernel [Z : ZeroObject C] (f : X ⟶ Y) := Equalizer f (Z.zero_morphism X Y)

structure BinaryProduct (X Y : C) :=
  (product             : C)
  (left_projection     : product ⟶ X)
  (right_projection    : product ⟶ Y)
  (map                 : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), Z ⟶ product)
  (left_factorisation  : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), (map f g) ≫ left_projection  = f . obviously) 
  (right_factorisation : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), (map f g) ≫ right_projection = g . obviously) 
  (uniqueness          : ∀ {Z : C} (f g : Z ⟶ product)
                            (left_witness  : f ≫ left_projection  = g ≫ left_projection )
                            (right_witness : f ≫ right_projection = g ≫ right_projection), f = g . obviously)

make_lemma BinaryProduct.left_factorisation
make_lemma BinaryProduct.right_factorisation
make_lemma BinaryProduct.uniqueness
attribute [simp,search] BinaryProduct.left_factorisation_lemma BinaryProduct.right_factorisation_lemma
attribute [applicable] BinaryProduct.left_projection BinaryProduct.right_projection BinaryProduct.map
attribute [applicable] BinaryProduct.uniqueness_lemma

structure Product {I : Type u₂} (F : I → C) :=
  (product       : C)
  (projection    : Π i : I, product ⟶ (F i))
  (map           : ∀ {Z : C} (f : Π i : I, Z ⟶ (F i)), Z ⟶ product)
  (factorisation : ∀ {Z : C} (f : Π i : I, Z ⟶ (F i)) (i : I), (map f) ≫ (projection i) = f i . obviously)
  (uniqueness    : ∀ {Z : C} (f g : Z ⟶ product) (witness : ∀ i : I, f ≫ (projection i) = g ≫ (projection i)), f = g . obviously)

make_lemma Product.factorisation
make_lemma Product.uniqueness
attribute [simp,search] Product.factorisation_lemma
attribute [applicable] Product.projection Product.map
attribute [applicable] Product.uniqueness_lemma

structure Coequalizer (f g : X ⟶ Y) :=
  (coequalizer   : C)
  (projection    : Y ⟶ coequalizer)
  (map           : ∀ {Z : C} (k : Y ⟶ Z) (w : f ≫ k = g ≫ k), coequalizer ⟶ Z)
  (witness       : f ≫ projection = g ≫ projection . obviously)
  (factorisation : ∀ {Z : C} (k : Y ⟶ Z) (w : f ≫ k = g ≫ k), projection ≫ (map k w) = k . obviously)
  (uniqueness    : ∀ {Z : C} (a b : coequalizer ⟶ Z) (witness : projection ≫ a = projection ≫ b), a = b . obviously)

make_lemma Coequalizer.witness
make_lemma Coequalizer.factorisation
make_lemma Coequalizer.uniqueness
attribute [simp,search] Coequalizer.factorisation_lemma
attribute [applicable] Coequalizer.projection Coequalizer.map
attribute [applicable] Coequalizer.uniqueness_lemma

definition Cokernel [Z : ZeroObject C] (f : X ⟶ Y) := Coequalizer f (Z.zero_morphism X Y)

structure BinaryCoproduct (X Y : C) :=
  (coproduct           : C)
  (left_inclusion      : X ⟶ coproduct)
  (right_inclusion     : Y ⟶ coproduct)
  (map                 : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), coproduct ⟶ Z)
  (left_factorisation  : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), left_inclusion ≫ (map f g)  = f . obviously) 
  (right_factorisation : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), right_inclusion ≫ (map f g) = g . obviously) 
  (uniqueness          : ∀ {Z : C} (f g : coproduct ⟶ Z)
                            (left_witness  : left_inclusion ≫ f = left_inclusion ≫ g)
                            (right_witness : right_inclusion ≫ f = right_inclusion ≫ g), f = g . obviously)

make_lemma BinaryCoproduct.left_factorisation
make_lemma BinaryCoproduct.right_factorisation
make_lemma BinaryCoproduct.uniqueness
attribute [simp,search] BinaryCoproduct.left_factorisation_lemma BinaryCoproduct.right_factorisation_lemma
attribute [applicable] BinaryCoproduct.left_inclusion BinaryCoproduct.right_inclusion BinaryCoproduct.map
attribute [applicable] BinaryCoproduct.uniqueness_lemma

structure Coproduct {I : Type u₂} (X : I → C) :=
  (coproduct     : C)
  (inclusion     : Π i : I, (X i) ⟶ coproduct)
  (map           : ∀ {Z : C} (f : Π i : I, (X i) ⟶ Z), coproduct ⟶ Z)
  (factorisation : ∀ {Z : C} (f : Π i : I, (X i) ⟶ Z) (i : I), (inclusion i) ≫ (map f) = f i . obviously)
  (uniqueness    : ∀ {Z : C} (f g : coproduct ⟶ Z) (witness : ∀ i : I, (inclusion i) ≫ f = (inclusion i) ≫ g), f = g . obviously)

-- PROJECT prove all these things are unique up to unique isomorphism
-- @[reducible] definition {u} unique_up_to_isomorphism (α : Type u) {C : Category} (f : α → C.Obj) := Π X Y : α, Isomorphism C (f X) (f Y)

end categories.universal

