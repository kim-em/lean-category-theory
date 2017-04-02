-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..natural_transformation
import ..graph

open tqft.categories
open tqft.categories.functor
open tqft.categories.isomorphism

namespace tqft.categories.universal

structure Cone { J C : Category } ( F : Functor J C ) :=
  ( limit : C.Obj )
  ( maps  : Π X : J.Obj, C.Hom limit (F X) )
  ( commutativity : Π X Y : J.Obj, Π f : J.Hom X Y, C.compose (maps X) (F.onMorphisms f) = maps Y )

local attribute [simp,ematch] Cone.commutativity

structure ConeMorphism { J C : Category } { F : Functor J C } ( X Y : Cone F ) :=
  ( morphism : C.Hom X.limit Y.limit )
  ( commutativity : Π P : J.Obj, C.compose morphism (Y.maps P) = (X.maps P) )

local attribute [simp,ematch] ConeMorphism.commutativity

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
  ( maps  : Π X : J.Obj, C.Hom (F X) colimit )
  ( commutativity : Π X Y : J.Obj, Π f : J.Hom X Y, C.compose (F.onMorphisms f) (maps Y) = maps X )

local attribute [simp,ematch] Cocone.commutativity

structure CoconeMorphism { J C : Category } { F : Functor J C } ( X Y : Cocone F ) :=
  ( morphism : C.Hom X.colimit Y.colimit )
  ( commutativity : Π P : J.Obj, C.compose (X.maps P) morphism = (Y.maps P) )

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

structure {u} Singleton ( α : Type u ) :=
  ( element : α )
  ( uniqueness : ∀ X Y : α, (X = Y) )

structure Equalizer { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) :=
  ( equalizer : C.Obj )
  ( inclusion : C.Hom equalizer X )
  ( witness   : C.compose inclusion f = C.compose inclusion g )
  ( factorisation : ∀ { Z : C.Obj } ( k : C.Hom Z X ) ( w : C.compose k f = C.compose k g ), Singleton { i : C.Hom Z equalizer // (C.compose i inclusion = k) } )

structure Product { C : Category } ( X Y : C.Obj ) :=
  ( product          : C.Obj )
  ( left_projection  : C.Hom product X )
  ( right_projection : C.Hom product Y )
  ( map : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), Singleton { i : C.Hom Z product // f = C.compose i left_projection ∧ g = C.compose i right_projection } )

structure Coequalizer { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) :=
  ( coequalizer : C.Obj )
  ( projection  : C.Hom Y coequalizer )
  ( witness     : C.compose f projection = C.compose g projection )
  ( factorisation : ∀ { Z : C.Obj } ( k : C.Hom Y Z ) ( w : C.compose f k = C.compose g k ), Singleton { p : C.Hom coequalizer Z // (C.compose projection p = k) } )

structure Coproduct { C : Category } ( X Y : C.Obj ) :=
  ( coproduct       : C.Obj )
  ( left_inclusion  : C.Hom X coproduct )
  ( right_inclusion : C.Hom Y coproduct )
  ( map : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), Singleton { p : C.Hom coproduct Z // f = C.compose left_inclusion p ∧ g = C.compose right_inclusion p } )

definition {u} unique_up_to_isomorphism ( α : Type u ) { C : Category } ( f : α → C.Obj ) := Π X Y : α, Isomorphism C (f X) (f Y)

lemma Equalizers_are_unique
  { C : Category }  
  { X Y : C.Obj } 
  ( f g : C.Hom X Y )
   : unique_up_to_isomorphism (Equalizer f g) Equalizer.equalizer
   := sorry -- PROJECT prove this via the comma category formulation, using lemmas in comparisons.lean

end tqft.categories.universal

