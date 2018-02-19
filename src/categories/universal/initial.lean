-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..functor_categories
import ..opposites
import tidy.its

open categories
open categories.isomorphism

namespace categories.initial

universe u

structure InitialObject (C : Type (u+1)) [category C] :=
  (initial_object                              : C)
  (morphism_from_initial_object_to             : ∀ Y : C, Hom initial_object Y)
  (uniqueness_of_morphisms_from_initial_object : ∀ Y : C, ∀ f g : Hom initial_object Y, f = g . obviously)

attribute [applicable] InitialObject.morphism_from_initial_object_to
make_lemma InitialObject.uniqueness_of_morphisms_from_initial_object
attribute [applicable,ematch] InitialObject.uniqueness_of_morphisms_from_initial_object_lemma

structure TerminalObject (C : Type (u+1)) [category C]  :=
  (terminal_object                            : C)
  (morphism_to_terminal_object_from           : ∀ Y : C, Hom Y terminal_object)
  (uniqueness_of_morphisms_to_terminal_object : ∀ Y : C, ∀ f g : Hom Y terminal_object, f = g . obviously)

attribute [applicable] TerminalObject.morphism_to_terminal_object_from
make_lemma TerminalObject.uniqueness_of_morphisms_to_terminal_object
attribute [applicable,ematch] TerminalObject.uniqueness_of_morphisms_to_terminal_object_lemma

variables {C : Type (u+1)} [category C]

instance InitialObject_coercion_to_object : has_coe (InitialObject C) C :=
  {coe := InitialObject.initial_object}

structure is_initial (X : C) :=
  (morphism_from_initial_object_to           : ∀ Y : C, Hom X Y)
  (uniqueness_of_morphisms_from_initial_object : ∀ Y : C, ∀ f g : Hom X Y, f = g)

-- We can't mark this as applicable, because that might generate goals that an object is initial!
-- attribute [ematch] is_initial.uniqueness_of_morphisms_from_initial_object

lemma InitialObjects_are_unique (X Y : InitialObject C) : @Isomorphism C _ X Y := ♯

instance TerminalObject_coercion_to_object : has_coe (TerminalObject C) C :=
  {coe := TerminalObject.terminal_object}

structure is_terminal (X : C) :=
  (morphism_to_terminal_object_from : ∀ Y : C, Hom Y X)
  (uniqueness_of_morphisms_to_terminal_object : ∀ Y : C, ∀ f g : Hom Y X, f = g) -- FIXME putting ' . obviously' here causes Lean to hang

lemma TerminalObjects_are_unique (X Y : TerminalObject C) : @Isomorphism C _ X Y := ♯

class ZeroObject (C : Type (u+1)) [category C] :=
  (zero_object : C)
  (is_initial  : is_initial  zero_object)
  (is_terminal : is_terminal zero_object)

definition ZeroObject.zero_morphism (Z : ZeroObject C) (X Y : C) : Hom X Y := (Z.is_terminal.morphism_to_terminal_object_from X) ≫ (Z.is_initial.morphism_from_initial_object_to Y) 

end categories.initial