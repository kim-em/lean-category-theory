-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .initial
import ..functor

open categories
open categories.functor
open categories.initial

namespace categories.universal

universes u v w
variables {J : Type (u+1)} [category J]
variables {C : Type (v+1)} [category C] {D : Type (w+1)} [category D]

structure Cone (F : Functor J C) :=
  (cone_point    : C)
  (cone_maps     : Π j : J, Hom cone_point (F j))
  (commutativity : Π {j k : J}, Π f : Hom j k, (cone_maps j) ≫ (F.onMorphisms f) = cone_maps k . obviously)

make_lemma Cone.commutativity
attribute [simp,ematch] Cone.commutativity_lemma

variable {F : Functor J C}

structure ConeMorphism (X Y : Cone F) : Type (max u v) :=
  (cone_morphism      : Hom X.cone_point Y.cone_point)
  (commutativity : Π j : J, cone_morphism ≫ (Y.cone_maps j) = (X.cone_maps j) . obviously)

make_lemma ConeMorphism.commutativity
attribute [simp,ematch] ConeMorphism.commutativity_lemma

@[simp,ematch] def ConeMorphism.commutativity_lemma_assoc {X Y : Cone F} (c : ConeMorphism X Y) (j : J) {Z : C} (z : Hom (F j) Z): c.cone_morphism ≫ Y.cone_maps j ≫ z = X.cone_maps j ≫ z :=
begin
rw ← category.associativity,
simp,
end

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
    cone_point    := G X.cone_point,
    cone_maps     := λ j, G.onMorphisms (X.cone_maps j)
 },
  onMorphisms   := λ X Y f, {
    cone_morphism := G.onMorphisms f.cone_morphism
 }
}

structure Cocone (F : Functor J C) :=
  (cocone_point  : C)
  (cocone_maps   : Π j : J, Hom (F j) cocone_point)
  (commutativity : Π {j k : J}, Π f : Hom j k, (F.onMorphisms f) ≫ (cocone_maps k) = cocone_maps j . obviously)

make_lemma Cocone.commutativity
attribute [simp,ematch] Cocone.commutativity_lemma

structure CoconeMorphism (X Y : Cocone F) : Type (max u v) :=
  (cocone_morphism      : Hom X.cocone_point Y.cocone_point)
  (commutativity : Π j : J, (X.cocone_maps j) ≫ cocone_morphism = (Y.cocone_maps j) . obviously)

make_lemma CoconeMorphism.commutativity
attribute [simp,ematch] CoconeMorphism.commutativity_lemma

@[simp,ematch] def CoconeMorphism.commutativity_lemma_assoc {X Y : Cocone F} (c : CoconeMorphism X Y) (j : J) {Z : C} (z : Hom Y.cocone_point Z): (X.cocone_maps j) ≫ c.cocone_morphism ≫ z = (Y.cocone_maps j) ≫ z :=
begin
rw ← category.associativity,
simp,
end


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
    cocone_point    := G X.cocone_point,
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

universes u v w
variables {J : Type (u+1)} [category J]
variables {C : Type (v+1)} [category C] {D : Type (w+1)} [category D]
variable {F : Functor J C}

open categories.universal

definition Functor.onCones (G : Functor C D) (c : Cone F) : Cone (FunctorComposition F G) := 
(Cones_functoriality F G) c
definition Functor.onCocones (G : Functor C D) (c : Cocone F) : Cocone (FunctorComposition F G) := 
(Cocones_functoriality F G) c

end categories.functor