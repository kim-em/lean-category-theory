-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .initial
import ..functor

open categories
open categories.functor
open categories.initial

namespace categories.universal

universes u
variables {J : Type u} [category J] {C : Type u} [category C] {D : Type u} [category D]

structure Cone (F : Functor J C) :=
  (cone_point    : C)
  (cone_maps     : Π j : J, Hom cone_point (F.onObjects j))
  (commutativity : Π {j k : J}, Π f : Hom j k, (cone_maps j) ≫ (F.onMorphisms f) = cone_maps k . obviously)

make_lemma Cone.commutativity
attribute [simp,ematch] Cone.commutativity_lemma

variable {F : Functor J C}

structure ConeMorphism (X Y : Cone F) :=
  (cone_morphism      : Hom X.cone_point Y.cone_point)
  (commutativity : Π j : J, cone_morphism ≫ (Y.cone_maps j) = (X.cone_maps j) . obviously)

make_lemma ConeMorphism.commutativity
attribute [simp,ematch] ConeMorphism.commutativity_lemma

@[applicable] lemma ConeMorphism_componentwise_equal
  {X Y : Cone F}
  {f g : ConeMorphism X Y}
  (w : f.cone_morphism = g.cone_morphism) : f = g :=
  begin
    induction f,
    induction g,
    tidy
  end

instance Cones (F : Functor J C) : category (Cone F) := {
  Hom            := λ X Y, ConeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ f.cone_morphism ≫ g.cone_morphism ⟩,
  identity       := λ X, ⟨ 𝟙 X.cone_point ⟩
}

definition Cones_functoriality (F : Functor J C) (G : Functor C D) : Functor (Cone F) (Cone (FunctorComposition F G)) := {
  onObjects     := λ X, {
    cone_point    := G.onObjects X.cone_point,
    cone_maps     := λ j, G.onMorphisms (X.cone_maps j)
 },
  onMorphisms   := λ X Y f, {
    cone_morphism := G.onMorphisms f.cone_morphism
 }
}

structure Cocone (F : Functor J C) :=
  (cocone_point  : C)
  (cocone_maps   : Π j : J, Hom (F.onObjects j) cocone_point)
  (commutativity : Π {j k : J}, Π f : Hom j k, (F.onMorphisms f) ≫ (cocone_maps k) = cocone_maps j . obviously)

make_lemma Cocone.commutativity
attribute [simp,ematch] Cocone.commutativity_lemma

structure CoconeMorphism (X Y : Cocone F) :=
  (cocone_morphism      : Hom X.cocone_point Y.cocone_point)
  (commutativity : Π j : J, (X.cocone_maps j) ≫ cocone_morphism = (Y.cocone_maps j) . obviously)

make_lemma CoconeMorphism.commutativity
attribute [simp,ematch] CoconeMorphism.commutativity_lemma

@[applicable] lemma CoconeMorphism_componentwise_equal
  {X Y : Cocone F}
  {f g : CoconeMorphism X Y}
  (w : f.cocone_morphism = g.cocone_morphism) : f = g :=
  begin
    induction f,
    induction g,
    tidy
  end

instance Cocones (F : Functor J C) : category (Cocone F) := {
  Hom            := λ X Y, CoconeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ f.cocone_morphism ≫ g.cocone_morphism ⟩,
  identity       := λ X, ⟨ 𝟙 X.cocone_point ⟩
}

definition Cocones_functoriality (F : Functor J C) (G : Functor C D) : Functor (Cocone F) (Cocone (FunctorComposition F G)) := {
  onObjects     := λ X, {
    cocone_point    := G.onObjects X.cocone_point,
    cocone_maps     := λ j, G.onMorphisms (X.cocone_maps j)
 },
  onMorphisms   := λ X Y f, {
    cocone_morphism := G.onMorphisms f.cocone_morphism
 }
}

definition LimitCone     (F : Functor J C) := TerminalObject (Cone F)
definition ColimitCocone (F : Functor J C) := InitialObject (Cocone F)

end categories.universal

namespace categories.functor

universes u
variables {J : Type u} [category J] {C : Type u} [category C] {D : Type u} [category D]
variable {F : Functor J C}

open categories.universal

definition Functor.onCones (G : Functor C D) (c : Cone F) : Cone (FunctorComposition F G) := 
(Cones_functoriality F G).onObjects c
definition Functor.onCocones (G : Functor C D) (c : Cocone F) : Cocone (FunctorComposition F G) := 
(Cocones_functoriality F G).onObjects c

-- TODO cleanup
-- @[simp] definition IdentityFunctor.onCones {C : Category} {J : Category} {F : Functor J C} (c : Cone F) : (IdentityFunctor C).onCones c = c

end categories.functor