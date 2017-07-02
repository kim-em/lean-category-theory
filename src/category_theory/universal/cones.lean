-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .initial
import ..functor

open categories
open categories.functor
open categories.initial

namespace categories.universal

structure Cone { J C : Category } ( F : Functor J C ) :=
  ( cone_point    : C.Obj )
  ( cone_maps     : Π j : J.Obj, C.Hom cone_point (F.onObjects j) )
  ( commutativity : Π { j k : J.Obj }, Π f : J.Hom j k, C.compose (cone_maps j) (F.onMorphisms f) = cone_maps k )

attribute [simp,ematch] Cone.commutativity

structure ConeMorphism { J C : Category } { F : Functor J C } ( X Y : Cone F ) :=
  ( cone_morphism      : C.Hom X.cone_point Y.cone_point )
  ( commutativity : Π j : J.Obj, C.compose cone_morphism (Y.cone_maps j) = (X.cone_maps j) )

attribute [simp,ematch] ConeMorphism.commutativity

@[pointwise] lemma ConeMorphism_componentwise_equal
  { J C : Category } { F : Functor J C } { X Y : Cone F }
  { f g : ConeMorphism X Y }
  ( w : f.cone_morphism = g.cone_morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

definition Cones { J C : Category } ( F : Functor J C ) : Category :=
{
  Obj            := Cone F,
  Hom            := λ X Y, ConeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ C.compose f.cone_morphism g.cone_morphism, ♮ ⟩,
  identity       := λ X, ⟨ C.identity X.cone_point, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

structure Cocone { J C : Category } ( F : Functor J C ) :=
  ( cocone_point  : C.Obj )
  ( cocone_maps   : Π j : J.Obj, C.Hom (F.onObjects j) cocone_point )
  ( commutativity : Π { j k : J.Obj }, Π f : J.Hom j k, C.compose (F.onMorphisms f) (cocone_maps k) = cocone_maps j )

attribute [simp,ematch] Cocone.commutativity

structure CoconeMorphism { J C : Category } { F : Functor J C } ( X Y : Cocone F ) :=
  ( cocone_morphism      : C.Hom X.cocone_point Y.cocone_point )
  ( commutativity : Π j : J.Obj, C.compose (X.cocone_maps j) cocone_morphism = (Y.cocone_maps j) )

attribute [simp,ematch] CoconeMorphism.commutativity

@[pointwise] lemma CoconeMorphism_componentwise_equal
  { J C : Category } { F : Functor J C } { X Y : Cocone F }
  { f g : CoconeMorphism X Y }
  ( w : f.cocone_morphism = g.cocone_morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

definition Cocones { J C : Category } ( F : Functor J C ) : Category :=
{
  Obj            := Cocone F,
  Hom            := λ X Y, CoconeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ C.compose f.cocone_morphism g.cocone_morphism, ♮ ⟩,
  identity       := λ X, ⟨ C.identity X.cocone_point, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition LimitCone   { J C : Category } ( F : Functor J C ) := TerminalObject (Cones F)
definition ColimitCone { J C : Category } ( F : Functor J C ) := InitialObject (Cocones F)

end categories.universal

