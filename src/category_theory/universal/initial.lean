-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..natural_transformation
import ..opposites

open tqft.categories
open tqft.categories.isomorphism

namespace tqft.categories.initial

structure InitialObject ( C : Category ) :=
  (object : C.Obj)
  (morphisms : ∀ Y : C.Obj, C.Hom object Y)
  (uniqueness : ∀ Y : C.Obj, ∀ f g : C.Hom object Y, f = g)

attribute [pointwise] InitialObject.morphisms
attribute [pointwise,ematch] InitialObject.uniqueness

instance InitialObject_coercion_to_object { C : Category } : has_coe (InitialObject C) (C.Obj) :=
  { coe := InitialObject.object }

structure is_initial { C : Category } ( X : C.Obj ) :=
  (morphism : ∀ Y : C.Obj, C.Hom X Y)
  (uniqueness :  ∀ Y : C.Obj, ∀ f : C.Hom X Y, f = morphism Y)

attribute [pointwise,ematch] is_initial.uniqueness

lemma InitialObjects_are_unique { C : Category } ( X Y : InitialObject C ) : Isomorphism C X Y := ♯

structure TerminalObject ( C : Category ) :=
  (object : C.Obj)
  (morphisms : ∀ Y : C.Obj, C.Hom Y object)
  (uniqueness : ∀ Y : C.Obj, ∀ f g : C.Hom Y object, f = g)

attribute [pointwise] TerminalObject.morphisms
attribute [pointwise,ematch] TerminalObject.uniqueness

instance TerminalObject_coercion_to_object { C : Category } : has_coe (TerminalObject C) (C.Obj) :=
  { coe := TerminalObject.object }

structure is_terminal { C : Category } ( X : C.Obj ) :=
  (morphism : ∀ Y : C.Obj, C.Hom Y X)
  (uniqueness :  ∀ Y : C.Obj, ∀ f : C.Hom Y X, f = morphism Y)

attribute [pointwise,ematch] is_terminal.uniqueness

lemma TerminalObjects_are_unique { C : Category } ( X Y : TerminalObject C ) : Isomorphism C X Y := ♯

class ZeroObject ( C : Category ) :=
  (object   : C.Obj)
  (initial  : is_initial  object)
  (terminal : is_terminal object)

definition ZeroObject.zero_morphism { C : Category } ( Z : ZeroObject C ) ( X Y : C.Obj ) : C.Hom X Y := C.compose (Z.terminal.morphism X) (Z.initial.morphism Y) 

end tqft.categories.initial