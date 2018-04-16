-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.opposites
import categories.equivalence
import categories.universal
import categories.universal.cones
import categories.universal.complete

open categories
open categories.functor
open categories.initial
open categories.opposites
open categories.universal
open categories.equivalence

namespace categories.universal.opposites

universes u₁ u₂ u₃

section
variable {C : Type (u₁+1)}
variable [category C]
variables {X Y : C}
variables {f g : X ⟶ Y}

def InitialObject_in_Opposite (i : InitialObject (Cᵒᵖ)) : TerminalObject C := {
  terminal_object := i.initial_object,
  morphism_to_terminal_object_from := i.morphism_from_initial_object_to,
  uniqueness_of_morphisms_to_terminal_object := i.uniqueness_of_morphisms_from_initial_object
}

def TerminalObject_in_Opposite (t : TerminalObject (Cᵒᵖ)) : InitialObject C := {
  initial_object := t.terminal_object,
  morphism_from_initial_object_to := t.morphism_to_terminal_object_from,
  uniqueness_of_morphisms_from_initial_object := t.uniqueness_of_morphisms_to_terminal_object
}

-- TODO: why can't we use tactics for witness factorisation and uniqueness?
def Coequalizer_from_Equalizer_in_Opposite         (e : @Equalizer (Cᵒᵖ) _ Y X f g)   : Coequalizer f g :=
  ⟨e.equalizer, e.inclusion, e.map, e.witness, e.factorisation, e.uniqueness⟩


def Equalizer_from_Coequalizer_in_Opposite         (e : @Coequalizer (Cᵒᵖ) _ Y X f g) : Equalizer f g :=
  ⟨e.coequalizer, e.projection, e.map, e.witness, e.factorisation, e.uniqueness⟩


def Coproduct_from_Product_in_Opposite             {I: Type u₃} {F : I → C}   (p : @Product (Cᵒᵖ) _ _ F)         : Coproduct F :=
  ⟨p.product, p.projection, p.map, p.factorisation ,p.uniqueness⟩


def Product_from_Coproduct_in_Opposite             {I: Type u₃} {F : I → C}   (p : @Coproduct (Cᵒᵖ) _ _ F)       : Product F :=
  ⟨p.coproduct, p.inclusion, p.map, p.factorisation ,p.uniqueness⟩


def BinaryCoproduct_from_BinaryProduct_in_Opposite (p : @BinaryProduct (Cᵒᵖ) _ X Y)   : BinaryCoproduct X Y :=
  ⟨p.product, p.left_projection, p.right_projection, p.map, p.left_factorisation, p.right_factorisation, p.uniqueness⟩



def BinaryProduct_from_BinaryCoproduct_in_Opposite (p : @BinaryCoproduct (Cᵒᵖ) _ X Y) : BinaryProduct X Y :=
  ⟨p.coproduct, p.left_inclusion, p.right_inclusion, p.map, p.left_factorisation, p.right_factorisation, p.uniqueness⟩
end

section
variable {J : Type (u₁+1)}
variable [category J]
variable {C : Type (u₂+1)}
variable [category C]


-- seems like a solid amount of data needed here.
def Cones_in_Opposite   (F : Functor J C) : Equivalence (Cone (OppositeFunctor F)) (Cocone F) :=
  ⟨ ⟨λ cone,⟨cone.cone_point,cone.cone_maps,sorry⟩,sorry,sorry,sorry⟩         -- functor Cone (OppositeFunctor F) → Cocone F
  , sorry
  , sorry
  , sorry⟩



def Cocones_in_Opposite (F : Functor J C) : Equivalence (Cocone (OppositeFunctor F)) (Cone F) := sorry
end

section
variable {C : Type (u₁+1)}
variable [category C]

instance Opposite_has_Products_of_has_Coproducts     [has_Coproducts C]   : has_Products (Cᵒᵖ) := ⟨sorry⟩
instance Opposite_has_Equalizers_of_has_Coequalizers [has_Coequalizers C] : has_Equalizers (Cᵒᵖ) := sorry
instance Opposite_has_Coproducts_of_has_Products     [has_Products C]     : has_Coproducts (Cᵒᵖ) := sorry
instance Opposite_has_Coequalizers_of_has_Equalizers [has_Equalizers C]   : has_Coequalizers (Cᵒᵖ) := sorry
end

section
variable {C : Type (u₁+2)}
variable [category C]

instance Opposite_Complete_of_Cocomplete [Cocomplete C]            : Complete (Cᵒᵖ) := sorry
instance Opposite_Cocomplete_of_Complete [Complete C]              : Cocomplete (Cᵒᵖ) := sorry

-- It doesn't make sense to have instances here; too many loops!
def Cocomplete_of_Opposite_Complete (C : Type (u₁+2)) [category C] [Complete (Cᵒᵖ)]   : Cocomplete C := sorry
def Complete_of_Opposite_Cocomplete (C : Type (u₁+2)) [category C] [Cocomplete (Cᵒᵖ)] : Complete C := sorry
end


end categories.universal.opposites
