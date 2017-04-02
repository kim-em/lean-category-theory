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
  (uniqueness : ∀ Y : C.Obj, ∀ f : C.Hom object Y, f = morphisms Y)

attribute [ematch] InitialObject.uniqueness

instance InitialObject_coercion_to_object { C : Category } : has_coe (InitialObject C) (C.Obj) :=
  { coe := InitialObject.object }

structure is_initial { C : Category } ( X : C.Obj ) :=
  (morphism : ∀ Y : C.Obj, C.Hom X Y)
  (uniqueness :  ∀ Y : C.Obj, ∀ f : C.Hom X Y, f = morphism Y)

attribute [ematch] is_initial.uniqueness

lemma InitialObjects_have_only_the_identity_endomorphism { C : Category } ( X: InitialObject C ) ( f : C.Hom X X ) : f = C.identity X :=
  begin
   blast, -- TODO blast is not actually doing anything here; but perhaps later it will.
   rewrite X.uniqueness X f,
   rewrite X.uniqueness X (C.identity X)
  end

lemma InitialObjects_are_unique { C : Category } ( X Y : InitialObject C ) : Isomorphism C X Y :=
  {
      morphism  := X.morphisms Y,
      inverse   := Y.morphisms X,
      witness_1 := begin apply InitialObjects_have_only_the_identity_endomorphism end,
      witness_2 := begin apply InitialObjects_have_only_the_identity_endomorphism end
  }

-- Do we dare:
definition TerminalObject ( C : Category ) := InitialObject (Opposite C)

-- If not:
-- structure TerminalObject ( C : Category ) :=
--   (object : C.Obj)
--   (morphisms : ∀ Y : C.Obj, C.Hom Y object)
--   (uniqueness : ∀ Y : C.Obj, ∀ f : C.Hom Y object, f = morphisms Y)

end tqft.categories.initial