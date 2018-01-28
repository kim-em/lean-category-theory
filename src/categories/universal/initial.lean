-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..functor_categories
import ..opposites

open categories
open categories.isomorphism

namespace categories.initial

structure InitialObject ( C : Category ) :=
  (initial_object                              : C.Obj)
  (morphism_from_initial_object_to             : ∀ Y : C.Obj, C.Hom initial_object Y)
  (uniqueness_of_morphisms_from_initial_object : ∀ Y : C.Obj, ∀ f g : C.Hom initial_object Y, f = g . tidy')

attribute [applicable] InitialObject.morphism_from_initial_object_to
make_lemma InitialObject.uniqueness_of_morphisms_from_initial_object
attribute [applicable,ematch] InitialObject.uniqueness_of_morphisms_from_initial_object_lemma

instance InitialObject_coercion_to_object { C : Category } : has_coe (InitialObject C) (C.Obj) :=
  { coe := InitialObject.initial_object }

structure is_initial { C : Category } ( X : C.Obj ) :=
  (morphism_from_initial_object_to           : ∀ Y : C.Obj, C.Hom X Y)
  (uniqueness_of_morphisms_from_initial_object : ∀ Y : C.Obj, ∀ f : C.Hom X Y, f = morphism_from_initial_object_to Y)

-- We can't mark this as applicable, because that might generate goals that an object is initial!
attribute [ematch] is_initial.uniqueness_of_morphisms_from_initial_object

lemma InitialObjects_are_unique { C : Category } ( X Y : InitialObject C ) : Isomorphism C X Y := ♯

structure TerminalObject ( C : Category ) :=
  (terminal_object                            : C.Obj)
  (morphism_to_terminal_object_from           : ∀ Y : C.Obj, C.Hom Y terminal_object)
  (uniqueness_of_morphisms_to_terminal_object : ∀ Y : C.Obj, ∀ f g : C.Hom Y terminal_object, f = g . tidy')

attribute [applicable] TerminalObject.morphism_to_terminal_object_from
make_lemma TerminalObject.uniqueness_of_morphisms_to_terminal_object
attribute [applicable,ematch] TerminalObject.uniqueness_of_morphisms_to_terminal_object_lemma

instance TerminalObject_coercion_to_object { C : Category } : has_coe (TerminalObject C) (C.Obj) :=
  { coe := TerminalObject.terminal_object }

structure is_terminal { C : Category } ( X : C.Obj ) :=
  (morphism_to_terminal_object_from : ∀ Y : C.Obj, C.Hom Y X)
  (uniqueness_of_morphisms_to_terminal_object :  ∀ Y : C.Obj, ∀ f : C.Hom Y X, f = morphism_to_terminal_object_from Y)

attribute [ematch] is_terminal.uniqueness_of_morphisms_to_terminal_object

lemma TerminalObjects_are_unique { C : Category } ( X Y : TerminalObject C ) : Isomorphism C X Y := ♯

class ZeroObject ( C : Category ) :=
  (zero_object : C.Obj)
  (is_initial  : is_initial  zero_object)
  (is_terminal : is_terminal zero_object)

definition ZeroObject.zero_morphism { C : Category } ( Z : ZeroObject C ) ( X Y : C.Obj ) : C.Hom X Y := C.compose (Z.is_terminal.morphism_to_terminal_object_from X) (Z.is_initial.morphism_from_initial_object_to Y) 

end categories.initial