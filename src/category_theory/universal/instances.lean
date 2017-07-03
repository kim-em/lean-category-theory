-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .universal
import ..util.finite

open categories
open categories.functor
open categories.isomorphism
open categories.initial
open categories.types
open categories.util
open categories.util.finite

namespace categories.universal

class has_InitialObject ( C : Category ) :=
  ( initial_object : InitialObject C )

class has_BinaryProducts ( C : Category ) :=
  ( binary_product : Π X Y : C.Obj, BinaryProduct X Y )
class has_FiniteProducts ( C : Category ) :=
  ( product : Π { I : Type } [ Finite I ] ( f : I → C.Obj ), Product f )
class has_Products ( C : Category ) :=
  ( product : Π { I : Type } ( f : I → C.Obj ), Product f )

class has_TerminalObject ( C : Category ) :=
  ( terminal_object : TerminalObject C )

class has_BinaryCoproducts ( C : Category ) :=
  ( binary_coproduct : Π X Y : C.Obj, BinaryCoproduct X Y )
class has_FiniteCoproducts ( C : Category ) :=
  ( coproduct : Π { I : Type } [ Finite I ] ( f : I → C.Obj ), Coproduct f )
class has_Coproducts ( C : Category ) :=
  ( coproduct : Π { I : Type } ( f : I → C.Obj ), Coproduct f )

class has_Equalizers ( C : Category ) :=
  ( equalizer : Π { X Y : C.Obj } ( f g : C.Hom X Y ), Equalizer f g )
class has_Coequalizers ( C : Category ) :=
  ( coequalizer : Π { X Y : C.Obj } ( f g : C.Hom X Y ), Coequalizer f g )

definition initial_object { C : Category } [ has_InitialObject C ] : C.Obj := has_InitialObject.initial_object C
definition terminal_object { C : Category } [ has_TerminalObject C ] : C.Obj := has_TerminalObject.terminal_object C

definition binary_product { C : Category } [ has_BinaryProducts C ] ( X Y : C.Obj ) := has_BinaryProducts.binary_product X Y
definition finite_product { C : Category } [ has_FiniteProducts C ] { I : Type } [ fin : Finite I ] ( f : I → C.Obj ) := @has_FiniteProducts.product C _ I fin f
definition product { C : Category } [ has_Products C ] { I : Type } ( F : I → C.Obj ) := has_Products.product F

definition binary_coproduct { C : Category } [ has_BinaryCoproducts C ] ( X Y : C.Obj ) := has_BinaryCoproducts.binary_coproduct X Y
definition finite_coproduct { C : Category } [ has_FiniteCoproducts C ] { I : Type } [ fin : Finite I ] ( f : I → C.Obj ) := @has_FiniteCoproducts.coproduct C _ I fin f
definition coproduct { C : Category } [ has_Coproducts C ] { I : Type } ( F : I → C.Obj ) := has_Coproducts.coproduct F

definition equalizer { C : Category } [ has_Equalizers C ] { X Y : C.Obj } ( f g : C.Hom X Y ) := has_Equalizers.equalizer f g
definition coequalizer { C : Category } [ has_Coequalizers C ] { X Y : C.Obj } ( f g : C.Hom X Y ) := has_Coequalizers.coequalizer f g

instance FiniteProducts_give_a_TerminalObject ( C : Category ) [ has_FiniteProducts C ] : has_TerminalObject C := {
  terminal_object :=
  let empty_product := @has_FiniteProducts.product C _ empty _ empty_function in {
    terminal_object                            := empty_product.product,
    morphism_to_terminal_object_from           := λ X, empty_product.map empty_dependent_function,
    uniqueness_of_morphisms_to_terminal_object := λ X f g, empty_product.uniqueness f g empty_dependent_function
  }
}
instance FiniteProducts_from_Products ( C : Category ) [ has_Products C ] : has_FiniteProducts C := {
  product := λ _ _ f, has_Products.product f
}
instance FiniteCoproducts_give_an_InitialObject ( C : Category ) [ has_FiniteCoproducts C ] : has_InitialObject C := {
  initial_object :=
  let empty_coproduct := @has_FiniteCoproducts.coproduct C _ empty _ empty_function in {
    initial_object                              := empty_coproduct.coproduct,
    morphism_from_initial_object_to             := λ X, empty_coproduct.map empty_dependent_function,
    uniqueness_of_morphisms_from_initial_object := λ X f g, empty_coproduct.uniqueness f g empty_dependent_function
  }
}
instance FiniteCoproducts_from_Coproducts ( C : Category ) [ has_Coproducts C ] : has_FiniteCoproducts C := {
  coproduct := λ _ _ f, has_Coproducts.coproduct f
}

instance BinaryProducts_from_FiniteProducts ( C : Category ) [ has_FiniteProducts C ] : has_BinaryProducts C := {
  binary_product := λ X Y : C.Obj,
    let F := Two.choice X Y in
    let p := finite_product F in {
      product             := p.product,
      left_projection     := p.projection Two._0,
      right_projection    := p.projection Two._1,
      map                 := λ _ f g, p.map (Two.dependent_choice f g),
      left_factorisation  := λ _ f g, p.factorisation (Two.dependent_choice f g) Two._0,
      right_factorisation := λ _ f g, p.factorisation (Two.dependent_choice f g) Two._1,
      uniqueness          := λ _ f g u v, p.uniqueness f g (Two.split_choice u v)
    }
}

-- PROJECT:
-- open nat

-- definition construct_finite_product ( C : Category ) [ has_TerminalObject C ] [ has_BinaryProducts C ]
--   : Π n : nat, Π ( I : Type ) ( fin : Finite I ) ( p : fin.cardinality = n ) ( f : I → C.Obj ), Product f
-- | 0        := λ { I : Type } [ fin : Finite I ] ( p : fin.cardinality = 0 ) ( f : I → C.Obj ), {
--                 product       := terminal_object,
--                 projection    := begin intros, admit end,
--                 map           := sorry,
--                 factorisation := sorry,
--                 uniqueness    := sorry
--               }
-- | (succ n) := sorry

-- instance FiniteProducts_from_BinaryProducts ( C : Category ) [ has_TerminalObject C ] [ has_BinaryProducts C ] : has_FiniteProducts C := {
--   product := λ { I : Type } [ fin : Finite I ] ( f : I → C.Obj ), construct_finite_product C fin.cardinality I fin ♯ f
-- }

end categories.universal

