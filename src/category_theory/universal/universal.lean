-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .initial
import ..isomorphism
import ..natural_transformation
import ..graph

open tqft.categories
open tqft.categories.functor
open tqft.categories.isomorphism
open tqft.categories.initial

namespace tqft.categories.universal

structure Cone { J C : Category } ( F : Functor J C ) :=
  ( limit : C.Obj )
  ( maps  : Π j : J.Obj, C.Hom limit (F.onObjects j) )
  ( commutativity : Π { j k : J.Obj }, Π f : J.Hom j k, C.compose (maps j) (F.onMorphisms f) = maps k )

attribute [simp,ematch] Cone.commutativity

structure ConeMorphism { J C : Category } { F : Functor J C } ( X Y : Cone F ) :=
  ( morphism : C.Hom X.limit Y.limit )
  ( commutativity : Π j : J.Obj, C.compose morphism (Y.maps j) = (X.maps j) )

attribute [simp,ematch] ConeMorphism.commutativity

@[pointwise] lemma ConeMorphism_componentwise_equal
  { J C : Category } { F : Functor J C } { X Y : Cone F }
  { f g : ConeMorphism X Y }
  ( w : f.morphism = g.morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

definition Cones { J C : Category } ( F : Functor J C ) : Category :=
{
  Obj            := Cone F,
  Hom            := λ X Y, ConeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ C.compose f.morphism g.morphism, ♮ ⟩,
  identity       := λ X, ⟨ C.identity X.limit, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

structure Cocone { J C : Category } ( F : Functor J C ) :=
  ( colimit : C.Obj )
  ( maps  : Π j : J.Obj, C.Hom (F.onObjects j) colimit )
  ( commutativity : Π { j k : J.Obj }, Π f : J.Hom j k, C.compose (F.onMorphisms f) (maps k) = maps j )

local attribute [simp,ematch] Cocone.commutativity

structure CoconeMorphism { J C : Category } { F : Functor J C } ( X Y : Cocone F ) :=
  ( morphism : C.Hom X.colimit Y.colimit )
  ( commutativity : Π j : J.Obj, C.compose (X.maps j) morphism = (Y.maps j) )

local attribute [simp,ematch] CoconeMorphism.commutativity

@[pointwise] lemma CoconeMorphism_componentwise_equal
  { J C : Category } { F : Functor J C } { X Y : Cocone F }
  { f g : CoconeMorphism X Y }
  ( w : f.morphism = g.morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

definition Cocones { J C : Category } ( F : Functor J C ) : Category :=
{
  Obj            := Cocone F,
  Hom            := λ X Y, CoconeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ C.compose f.morphism g.morphism, ♮ ⟩,
  identity       := λ X, ⟨ C.identity X.colimit, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition Limit   { J C : Category } ( F : Functor J C ) := TerminalObject (Cones F)
definition Colimit { J C : Category } ( F : Functor J C ) := InitialObject (Cocones F)

structure Equalizer { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) :=
  ( equalizer : C.Obj )
  ( inclusion : C.Hom equalizer X )
  ( witness   : C.compose inclusion f = C.compose inclusion g )
  ( map : ∀ { Z : C.Obj } ( k : C.Hom Z X ) ( w : C.compose k f = C.compose k g ), C.Hom Z equalizer )
  ( factorisation : ∀ { Z : C.Obj } ( k : C.Hom Z X ) ( w : C.compose k f = C.compose k g ), C.compose (map k w) inclusion = k )
  ( uniqueness : ∀ { Z : C.Obj } ( a b : C.Hom Z equalizer ) ( witness : C.compose a inclusion = C.compose b inclusion ), a = b )

attribute [simp,ematch] Equalizer.factorisation
attribute [pointwise] Equalizer.inclusion Equalizer.map
attribute [pointwise] Equalizer.uniqueness

structure Product { C : Category } ( X Y : C.Obj ) :=
  ( product          : C.Obj )
  ( left_projection  : C.Hom product X )
  ( right_projection : C.Hom product Y )
  ( map : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.Hom Z product )
  ( left_factorisation  : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.compose (map f g) left_projection  = f ) 
  ( right_factorisation : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.compose (map f g) right_projection = g ) 
  ( uniqueness : ∀ { Z : C.Obj } ( f g : C.Hom Z product )
                   ( left_witness  : C.compose f left_projection  = C.compose g left_projection  )
                   ( right_witness : C.compose f right_projection = C.compose g right_projection ), f = g )

attribute [simp,ematch] Product.left_factorisation Product.right_factorisation 
attribute [pointwise] Product.left_projection Product.right_projection Product.map
attribute [pointwise] Product.uniqueness

-- definition {u} subtype.val_eq { α : Type u } { P : α → Prop } { X Y : { a : α // P a } } ( h : X = Y ) : X.val = Y.val := ♮

structure Coequalizer { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) :=
  ( coequalizer : C.Obj )
  ( projection : C.Hom Y coequalizer )
  ( witness   : C.compose f projection = C.compose g projection )
  ( map : ∀ { Z : C.Obj } ( k : C.Hom Y Z ) ( w : C.compose f k = C.compose g k ), C.Hom coequalizer Z )
  ( factorisation : ∀ { Z : C.Obj } ( k : C.Hom Y Z ) ( w : C.compose f k = C.compose g k ), C.compose projection (map k w) = k )
  ( uniqueness : ∀ { Z : C.Obj } ( a b : C.Hom coequalizer Z ) ( witness : C.compose projection a = C.compose projection b ), a = b )

attribute [simp,ematch] Coequalizer.factorisation
attribute [pointwise] Coequalizer.projection Coequalizer.map
attribute [pointwise] Coequalizer.uniqueness

structure Coproduct { C : Category } ( X Y : C.Obj ) :=
  ( coproduct          : C.Obj )
  ( left_inclusion  : C.Hom X coproduct )
  ( right_inclusion : C.Hom Y coproduct )
  ( map : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.Hom coproduct Z )
  ( left_factorisation  : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.compose left_inclusion (map f g)  = f ) 
  ( right_factorisation : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.compose right_inclusion(map f g) = g ) 
  ( uniqueness : ∀ { Z : C.Obj } ( f g : C.Hom coproduct Z )
                   ( left_witness  : C.compose left_inclusion f = C.compose left_inclusion g )
                   ( right_witness : C.compose right_inclusion f = C.compose right_inclusion g ), f = g )

attribute [simp,ematch] Coproduct.left_factorisation Coproduct.right_factorisation 
attribute [pointwise] Coproduct.left_inclusion Coproduct.right_inclusion Coproduct.map
attribute [pointwise] Coproduct.uniqueness

@[reducible] definition {u} unique_up_to_isomorphism ( α : Type u ) { C : Category } ( f : α → C.Obj ) := Π X Y : α, Isomorphism C (f X) (f Y)

class has_TerminalObject ( C : Category ) :=
  ( terminal_object : TerminalObject C )
class has_FiniteProducts ( C : Category ) extends has_TerminalObject C :=
  ( binary_product : Π X Y : C.Obj, Product X Y )
class has_InitialObject ( C : Category ) :=
  ( initial_object : InitialObject C )
class has_FiniteCoproducts ( C : Category ) extends has_InitialObject C :=
  ( binary_coproduct : Π X Y : C.Obj, Coproduct X Y )
class has_Equalizers ( C : Category ) :=
  ( equalizer : Π { X Y : C.Obj } ( f g : C.Hom X Y ), Equalizer f g )
class has_Coequalizers ( C : Category ) :=
  ( coequalizer : Π { X Y : C.Obj } ( f g : C.Hom X Y ), Coequalizer f g )

definition product { C : Category } [ has_FiniteProducts C ] ( X Y : C.Obj ) := has_FiniteProducts.binary_product X Y
definition terminal_object { C : Category } [ has_TerminalObject C ] : C.Obj := has_TerminalObject.terminal_object C
definition coproduct { C : Category } [ has_FiniteCoproducts C ] ( X Y : C.Obj ) := has_FiniteCoproducts.binary_coproduct X Y
definition initial_object { C : Category } [ has_InitialObject C ] : C.Obj := has_InitialObject.initial_object C
definition equalizer { C : Category } [ has_Equalizers C ] { X Y : C.Obj } ( f g : C.Hom X Y ) := has_Equalizers.equalizer f g
definition coequalizer { C : Category } [ has_Coequalizers C ] { X Y : C.Obj } ( f g : C.Hom X Y ) := has_Coequalizers.coequalizer f g
-- PROJECT construct finite (co)products from these

end tqft.categories.universal

