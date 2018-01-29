-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .cones
import ..util.hlist
import ..util.finite

open categories
open categories.functor
open categories.isomorphism
open categories.initial
open categories.types
open categories.util
open categories.util.finite

namespace categories.universal

structure Equalizer { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) :=
  ( equalizer     : C.Obj )
  ( inclusion     : C.Hom equalizer X )
  ( map           : ∀ { Z : C.Obj } ( k : C.Hom Z X ) ( w : C.compose k f = C.compose k g ), C.Hom Z equalizer )
  ( witness       : C.compose inclusion f = C.compose inclusion g . tidy' )
  ( factorisation : ∀ { Z : C.Obj } ( k : C.Hom Z X ) ( w : C.compose k f = C.compose k g ), C.compose (map k w) inclusion = k . tidy' )
  ( uniqueness    : ∀ { Z : C.Obj } ( a b : C.Hom Z equalizer ) ( witness : C.compose a inclusion = C.compose b inclusion ), a = b . tidy')

-- Or should we write out yet another structure, and prove it agrees with the equalizer?
definition Kernel { C : Category } [ Z : ZeroObject C ] { X Y : C.Obj } ( f : C.Hom X Y ) := Equalizer f ( Z.zero_morphism X Y )

make_lemma Equalizer.witness
make_lemma Equalizer.factorisation
make_lemma Equalizer.uniqueness
attribute [ematch] Equalizer.factorisation_lemma
attribute [applicable] Equalizer.inclusion Equalizer.map
attribute [applicable] Equalizer.uniqueness_lemma

structure BinaryProduct { C : Category } ( X Y : C.Obj ) :=
  ( product             : C.Obj )
  ( left_projection     : C.Hom product X )
  ( right_projection    : C.Hom product Y )
  ( map                 : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.Hom Z product )
  ( left_factorisation  : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.compose (map f g) left_projection  = f . tidy' ) 
  ( right_factorisation : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.compose (map f g) right_projection = g . tidy' ) 
  ( uniqueness          : ∀ { Z : C.Obj } ( f g : C.Hom Z product )
                            ( left_witness  : C.compose f left_projection  = C.compose g left_projection  )
                            ( right_witness : C.compose f right_projection = C.compose g right_projection ), f = g . tidy' )

make_lemma BinaryProduct.left_factorisation
make_lemma BinaryProduct.right_factorisation
make_lemma BinaryProduct.uniqueness
attribute [ematch] BinaryProduct.left_factorisation_lemma BinaryProduct.right_factorisation_lemma
attribute [applicable] BinaryProduct.left_projection BinaryProduct.right_projection BinaryProduct.map
attribute [applicable] BinaryProduct.uniqueness_lemma

structure Product { C : Category } { I : Type } ( F : I → C.Obj ) :=
  ( product       : C.Obj )
  ( projection    : Π i : I, C.Hom product (F i) )
  ( map           : ∀ { Z : C.Obj } ( f : Π i : I, C.Hom Z (F i) ), C.Hom Z product )
  ( factorisation : ∀ { Z : C.Obj } ( f : Π i : I, C.Hom Z (F i) ) ( i : I ), C.compose (map f) (projection i) = f i . tidy' )
  ( uniqueness    : ∀ { Z : C.Obj } ( f g : C.Hom Z product ) ( witness : ∀ i : I, C.compose f (projection i) = C.compose g (projection i)), f = g . tidy' )

make_lemma Product.factorisation
make_lemma Product.uniqueness
attribute [ematch] Product.factorisation_lemma
attribute [applicable] Product.projection Product.map
attribute [applicable] Product.uniqueness_lemma

structure Coequalizer { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) :=
  ( coequalizer   : C.Obj )
  ( projection    : C.Hom Y coequalizer )
  ( witness       : C.compose f projection = C.compose g projection )
  ( map           : ∀ { Z : C.Obj } ( k : C.Hom Y Z ) ( w : C.compose f k = C.compose g k ), C.Hom coequalizer Z )
  ( factorisation : ∀ { Z : C.Obj } ( k : C.Hom Y Z ) ( w : C.compose f k = C.compose g k ), C.compose projection (map k w) = k )
  ( uniqueness    : ∀ { Z : C.Obj } ( a b : C.Hom coequalizer Z ) ( witness : C.compose projection a = C.compose projection b ), a = b )

attribute [simp,ematch] Coequalizer.factorisation
attribute [applicable] Coequalizer.projection Coequalizer.map
attribute [applicable] Coequalizer.uniqueness

definition Cokernel { C : Category } [ Z : ZeroObject C ] { X Y : C.Obj } ( f : C.Hom X Y ) := Coequalizer f ( Z.zero_morphism X Y )

structure BinaryCoproduct { C : Category } ( X Y : C.Obj ) :=
  ( coproduct           : C.Obj )
  ( left_inclusion      : C.Hom X coproduct )
  ( right_inclusion     : C.Hom Y coproduct )
  ( map                 : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.Hom coproduct Z )
  ( left_factorisation  : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.compose left_inclusion (map f g)  = f ) 
  ( right_factorisation : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.compose right_inclusion(map f g) = g ) 
  ( uniqueness          : ∀ { Z : C.Obj } ( f g : C.Hom coproduct Z )
                            ( left_witness  : C.compose left_inclusion f = C.compose left_inclusion g )
                            ( right_witness : C.compose right_inclusion f = C.compose right_inclusion g ), f = g )

attribute [simp,ematch] BinaryCoproduct.left_factorisation BinaryCoproduct.right_factorisation 
attribute [applicable] BinaryCoproduct.left_inclusion BinaryCoproduct.right_inclusion BinaryCoproduct.map
attribute [applicable] BinaryCoproduct.uniqueness

structure Coproduct { C : Category } { I : Type } ( X : I → C.Obj ) :=
  ( coproduct     : C.Obj )
  ( inclusion     : Π i : I, C.Hom (X i) coproduct )
  ( map           : ∀ { Z : C.Obj } ( f : Π i : I, C.Hom (X i) Z ), C.Hom coproduct Z )
  ( factorisation : ∀ { Z : C.Obj } ( f : Π i : I, C.Hom (X i) Z ) ( i : I ), C.compose (inclusion i) (map f) = f i )
  ( uniqueness    : ∀ { Z : C.Obj } ( f g : C.Hom coproduct Z ) ( witness : ∀ i : I, C.compose (inclusion i) f = C.compose (inclusion i) g), f = g )

@[reducible] definition {u} unique_up_to_isomorphism ( α : Type u ) { C : Category } ( f : α → C.Obj ) := Π X Y : α, Isomorphism C (f X) (f Y)

end categories.universal

