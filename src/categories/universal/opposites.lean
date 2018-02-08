-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..opposites
import ..equivalence
import .cones
import .universal
import .complete

open categories
open categories.functor
open categories.initial
open categories.opposites
open categories.universal
open categories.equivalence

namespace categories.universal.opposites

universes u₁ u₂ u₃

def InitialObject_in_Opposite {C : Category.{u₁ u₂}} (i : InitialObject (Opposite C)) : TerminalObject C := {
  terminal_object := i.initial_object,
  morphism_to_terminal_object_from := i.morphism_from_initial_object_to,
  uniqueness_of_morphisms_to_terminal_object := i.uniqueness_of_morphisms_from_initial_object
}

def TerminalObject_in_Opposite {C : Category.{u₁ u₂}} (t : TerminalObject (Opposite C)) : InitialObject C := {
  initial_object := t.terminal_object,
  morphism_from_initial_object_to := t.morphism_to_terminal_object_from,
  uniqueness_of_morphisms_from_initial_object := t.uniqueness_of_morphisms_to_terminal_object
}

def Coequalizer_from_Equalizer_in_Opposite          {C : Category.{u₁ u₂}} {X Y : C.Obj} {f g : C.Hom X Y} (e : @Equalizer (Opposite C) Y X f g)   : Coequalizer f g := sorry
def Equalizer_from_Coequalizer_in_Opposite          {C : Category.{u₁ u₂}} {X Y : C.Obj} {f g : C.Hom X Y} (e : @Coequalizer (Opposite C) Y X f g) : Equalizer f g := sorry
def Coproduct_from_Product_in_Opposite              {C : Category.{u₁ u₂}} {I: Type u₃} {F : I → C.Obj}   (p : @Product (Opposite C) _ F)         : Coproduct F := sorry
def Product_from_Coproduct_in_Opposite              {C : Category.{u₁ u₂}} {I: Type u₃} {F : I → C.Obj}   (p : @Coproduct (Opposite C) _ F)       : Product F := sorry
def BinaryCoproduct_from_BinaryProduct_in_Opposite {C : Category.{u₁ u₂}} {X Y : C.Obj}                    (p : @BinaryProduct (Opposite C) X Y)   : BinaryCoproduct X Y := sorry
def BinaryProduct_from_BinaryCoproduct_in_Opposite  {C : Category.{u₁ u₂}} {X Y : C.Obj}                   (p : @BinaryCoproduct (Opposite C) X Y) : BinaryProduct X Y := sorry

def Cones_in_Opposite   {J C : Category} (F : Functor J C) : Equivalence (Cones (OppositeFunctor F)) (Cocones F) := sorry
def Cocones_in_Opposite {J C : Category} (F : Functor J C) : Equivalence (Cocones (OppositeFunctor F)) (Cones F) := sorry

instance Opposite_has_Products_of_has_Coproducts     {C : Category} [c : has_Coproducts C]   : has_Products (Opposite C) := sorry
instance Opposite_has_Equalizers_of_has_Coequalizers {C : Category} [c : has_Coequalizers C] : has_Equalizers (Opposite C) := sorry
instance Opposite_has_Coproducts_of_has_Products     {C : Category} [c : has_Products C]     : has_Coproducts (Opposite C) := sorry
instance Opposite_has_Coequalizers_of_has_Equalizers {C : Category} [c : has_Equalizers C]   : has_Coequalizers (Opposite C) := sorry

instance Opposite_Complete_of_Cocomplete {C : Category} [c : Cocomplete C]            : Complete (Opposite C) := sorry
instance Opposite_Cocomplete_of_Complete {C : Category} [c : Complete C]              : Cocomplete (Opposite C) := sorry

-- It doesn't make sense to have instances here; too many loops!
def Cocomplete_of_Opposite_Complete (C : Category) [ Complete (Opposite C) ]   : Cocomplete C := sorry
def Complete_of_Opposite_Cocomplete (C : Category) [ Cocomplete (Opposite C) ] : Complete C := sorry

end categories.universal.opposites