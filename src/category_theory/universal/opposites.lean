-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Daniel Barter

import category_theory.opposites
import category_theory.equivalence
import category_theory.universal
import category_theory.universal.cones
import category_theory.universal.complete

open category_theory
open category_theory.initial
open category_theory.universal

namespace category_theory.universal.opposites

universes u₁ u₂ u₃

section
variable {C : Type (u₁+1)}
variable [large_category C]
variables {X Y : C}
variables {f g : X ⟶ Y}

def initial_object_in_opposite (i : initial_object (Cᵒᵖ)) : terminal_object C := 
{ obj := i.obj,
  «from» := i.to,
  uniqueness := i.uniqueness }

def terminal_object_in_opposite (t : terminal_object (Cᵒᵖ)) : initial_object C := 
{ obj := t.obj,
  to := t.«from»,
  uniqueness := t.uniqueness }

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

def Cones_in_Opposite_functor (F : J ↝ C) : (Cone (F.op))ᵒᵖ ↝ (Cocone F)  := 
{ obj := λ c, ⟨c.cone_point, c.cone_maps, begin tidy, erw c.commutativity_lemma, end⟩, -- PROJECT (Scott) why can't rewrite_search handle this one?
  map' := λ X Y f, ⟨f.cone_morphism, begin tidy, erw f.commutativity_lemma, end⟩ }

def Cocones_in_Opposite (F : J ↝ C) : Equivalence ((Cocone (F.op))ᵒᵖ) (Cone F) := sorry
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


end category_theory.universal.opposites
