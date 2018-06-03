-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Daniel Barter

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
variable [large_category C]
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
def Coequalizer_from_Equalizer_in_Opposite         (e : @Equalizer.{u₁+1 u₁} (Cᵒᵖ) _ Y X f g)   : Coequalizer f g :=
  ⟨e.equalizer, e.inclusion, e.map, e.witness, e.factorisation, e.uniqueness⟩


def Equalizer_from_Coequalizer_in_Opposite         (e : @Coequalizer.{u₁+1 u₁} (Cᵒᵖ) _ Y X f g) : Equalizer f g :=
  ⟨e.coequalizer, e.projection, e.map, e.witness, e.factorisation, e.uniqueness⟩


def Coproduct_from_Product_in_Opposite             {I: Type u₃} {F : I → C}   (p : @Product.{u₁+1 u₁} (Cᵒᵖ) _ _ F)         : Coproduct.{u₁+1 u₁} F :=
  ⟨p.product, p.projection, p.map, p.factorisation ,p.uniqueness⟩


def Product_from_Coproduct_in_Opposite             {I: Type u₃} {F : I → C}   (p : @Coproduct.{u₁+1 u₁} (Cᵒᵖ) _ _ F)       : Product.{u₁+1 u₁} F :=
  ⟨p.coproduct, p.inclusion, p.map, p.factorisation ,p.uniqueness⟩


def BinaryCoproduct_from_BinaryProduct_in_Opposite (p : @BinaryProduct.{u₁+1 u₁} (Cᵒᵖ) _ X Y)   : BinaryCoproduct.{u₁+1 u₁} X Y :=
  ⟨p.product, p.left_projection, p.right_projection, p.map, p.left_factorisation, p.right_factorisation, p.uniqueness⟩



def BinaryProduct_from_BinaryCoproduct_in_Opposite (p : @BinaryCoproduct.{u₁+1 u₁} (Cᵒᵖ) _ X Y) : BinaryProduct.{u₁+1 u₁} X Y :=
  ⟨p.coproduct, p.left_inclusion, p.right_inclusion, p.map, p.left_factorisation, p.right_factorisation, p.uniqueness⟩
end

section
variable {J : Type u₁}
variable [small_category J]
variable {C : Type (u₁+1)}
variable [large_category C]

def Cones_in_Opposite_functor (F : J ↝ C) : (Cone (OppositeFunctor F))ᵒᵖ ↝ (Cocone F)  := 
{ onObjects   := λ c, ⟨c.cone_point, c.cone_maps, begin tidy, erw c.commutativity_lemma, end⟩, -- PROJECT (Scott) why can't rewrite_search handle this one?
  onMorphisms := λ X Y f, ⟨f.cone_morphism, begin tidy, erw f.commutativity_lemma, end⟩ }

def Cocones_in_Opposite (F : J ↝ C) : Equivalence ((Cocone (OppositeFunctor F))ᵒᵖ) (Cone F) := sorry
end

section
variable {C : Type (u₁+1)}
variable [large_category C]

instance Opposite_has_Products_of_has_Coproducts     [has_Coproducts C]   : has_Products (Cᵒᵖ) := ⟨sorry⟩
instance Opposite_has_Equalizers_of_has_Coequalizers [has_Coequalizers.{u₁+1 u₁} C] : has_Equalizers.{u₁+1 u₁} (Cᵒᵖ) := sorry
instance Opposite_has_Coproducts_of_has_Products     [has_Products C]     : has_Coproducts (Cᵒᵖ) := sorry
instance Opposite_has_Coequalizers_of_has_Equalizers [has_Equalizers.{u₁+1 u₁} C]   : has_Coequalizers.{u₁+1 u₁} (Cᵒᵖ) := sorry
end

section
variable {C : Type (u₁+1)}
variable [large_category C]

instance Opposite_Complete_of_Cocomplete [Cocomplete C]            : Complete (Cᵒᵖ) := sorry
instance Opposite_Cocomplete_of_Complete [Complete C]              : Cocomplete (Cᵒᵖ) := sorry
end

-- It doesn't make sense to have instances here; too many loops!
def Cocomplete_of_Opposite_Complete (C : Type (u₁+1)) [large_category C] [Complete (Cᵒᵖ)]   : Cocomplete C := sorry
def Complete_of_Opposite_Cocomplete (C : Type (u₁+1)) [large_category C] [Cocomplete (Cᵒᵖ)] : Complete C := sorry


end categories.universal.opposites
