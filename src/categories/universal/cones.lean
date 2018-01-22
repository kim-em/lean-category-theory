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
  ( commutativity : Π { j k : J.Obj }, Π f : J.Hom j k, C.compose (cone_maps j) (F.onMorphisms f) = cone_maps k . tidy' )

make_lemma Cone.commutativity
attribute [ematch] Cone.commutativity_lemma

structure ConeMorphism { J C : Category } { F : Functor J C } ( X Y : Cone F ) :=
  ( cone_morphism      : C.Hom X.cone_point Y.cone_point )
  ( commutativity : Π j : J.Obj, C.compose cone_morphism (Y.cone_maps j) = (X.cone_maps j) . tidy' )

make_lemma ConeMorphism.commutativity
attribute [ematch] ConeMorphism.commutativity_lemma

@[applicable] lemma ConeMorphism_componentwise_equal
  { J C : Category } { F : Functor J C } { X Y : Cone F }
  { f g : ConeMorphism X Y }
  ( w : f.cone_morphism = g.cone_morphism ) : f = g :=
  begin
    induction f,
    induction g,
    tidy
  end

definition Cones { J C : Category } ( F : Functor J C ) : Category :=
{
  Obj            := Cone F,
  Hom            := λ X Y, ConeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ C.compose f.cone_morphism g.cone_morphism ⟩,
  identity       := λ X, ⟨ C.identity X.cone_point ⟩
}

definition Cones_functoriality { J C D : Category } ( F : Functor J C ) ( G : Functor C D ) : Functor (Cones F) (Cones (FunctorComposition F G)) := {
  onObjects     := λ X, {
    cone_point    := G.onObjects X.cone_point,
    cone_maps     := λ j, G.onMorphisms (X.cone_maps j)
  },
  onMorphisms   := λ X Y f, {
    cone_morphism := G.onMorphisms f.cone_morphism
  }
}

structure Cocone { J C : Category } ( F : Functor J C ) :=
  ( cocone_point  : C.Obj )
  ( cocone_maps   : Π j : J.Obj, C.Hom (F.onObjects j) cocone_point )
  ( commutativity : Π { j k : J.Obj }, Π f : J.Hom j k, C.compose (F.onMorphisms f) (cocone_maps k) = cocone_maps j . tidy' )

make_lemma Cocone.commutativity
attribute [ematch] Cocone.commutativity_lemma

structure CoconeMorphism { J C : Category } { F : Functor J C } ( X Y : Cocone F ) :=
  ( cocone_morphism      : C.Hom X.cocone_point Y.cocone_point )
  ( commutativity : Π j : J.Obj, C.compose (X.cocone_maps j) cocone_morphism = (Y.cocone_maps j) . tidy' )

make_lemma CoconeMorphism.commutativity
attribute [ematch] CoconeMorphism.commutativity_lemma

@[applicable] lemma CoconeMorphism_componentwise_equal
  { J C : Category } { F : Functor J C } { X Y : Cocone F }
  { f g : CoconeMorphism X Y }
  ( w : f.cocone_morphism = g.cocone_morphism ) : f = g :=
  begin
    induction f,
    induction g,
    tidy
  end

definition Cocones { J C : Category } ( F : Functor J C ) : Category :=
{
  Obj            := Cocone F,
  Hom            := λ X Y, CoconeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ C.compose f.cocone_morphism g.cocone_morphism ⟩,
  identity       := λ X, ⟨ C.identity X.cocone_point ⟩
}

definition LimitCone   { J C : Category } ( F : Functor J C ) := TerminalObject (Cones F)
definition ColimitCone { J C : Category } ( F : Functor J C ) := InitialObject (Cocones F)

end categories.universal

