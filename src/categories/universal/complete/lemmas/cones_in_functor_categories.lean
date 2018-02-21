-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ...complete

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.isomorphism
open categories.initial
open categories.universal

namespace categories.universal.lemmas.cones_in_functor_categories

universes j u₁ u₂

variable {J : Type (j+1)}
variable [category J]
variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

@[applicable] lemma uniqueness_of_morphisms_to_terminal_object_cone_point 
  {Z : D}
  {G : Functor J D}
  {L : LimitCone G}
  (cone_maps : Π j : J, Hom Z (G j)) 
  (commutativity : Π j k : J, Π f : Hom j k, (cone_maps j) ≫ (G &> f) = cone_maps k)
  (f g : Hom Z L.terminal_object.cone_point)
  (commutativity_f : Π j : J, f ≫ (L.terminal_object.cone_maps j) = cone_maps j)
  (commutativity_g : Π j : J, g ≫ (L.terminal_object.cone_maps j) = cone_maps j)
   : f = g :=
begin
  let cone : Cone G := {
    cone_point    := Z,
    cone_maps     := cone_maps,
    commutativity := commutativity
 },
  let cone_morphism_f : ConeMorphism cone L.terminal_object := {
    cone_morphism := f,
    commutativity := commutativity_f
 },
  let cone_morphism_g : ConeMorphism cone L.terminal_object := {
    cone_morphism := g,
    commutativity := commutativity_g
 },
  exact congr_arg ConeMorphism.cone_morphism (L.uniqueness_of_morphisms_to_terminal_object cone cone_morphism_f cone_morphism_g), 
end

lemma bifunctor_naturality  
(F : Functor J (Functor C D))
(X Y : C)
(f : Hom X Y)
(j k : J)
(g : Hom j k)
  : ((F j) &> f) ≫ ((F &> g).components Y)
  = ((F &> g).components X) ≫ ((F k) &> f) := ♯

@[simp] lemma cone_in_functor_category 
(F : Functor J (Functor C D))
(X Y : C)
(f : Hom X Y)
(j k : J)
(g : Hom j k)
(cone : Cone F)
: ((cone.cone_maps j).components X) ≫ ((F j) &> f) ≫ 
      ((F &> g).components Y) =
    ((cone.cone_maps k).components X) ≫ ((F k) &> f) :=
begin
  have p := cone.commutativity g,
  have p' := congr_arg NaturalTransformation.components p,
  have p'' := congr_fun p' X,
  obviously,
end

@[simp] lemma cone_in_functor_category_naturality
(F : Functor J (Functor C D))
(X Y : C)
(f : Hom X Y)
(j : J)
(cone : universal.Cone F)
  : ((cone.cone_point) &> f) ≫ ((cone.cone_maps j).components Y) =
    ((cone.cone_maps j).components X) ≫ ((F j) &> f) := ♯

@[simp] lemma cone_commutativity_in_FunctorCategory
(F : Functor J (Functor C D))
(X : C)
(j k : J)
(f : Hom j k) 
(Y : Cone F)
 : ((Y.cone_maps j).components X) ≫ ((F &> f).components X) = (Y.cone_maps k).components X := 
begin
 have p := Y.commutativity f,
 have p' := congr_arg NaturalTransformation.components p,
 tidy,
end

@[simp] lemma cone_commutativity_in_FunctorCategory_assoc
(F : Functor J (Functor C D))
(X : C)
(j k : J)
(f : Hom j k) 
(Y : Cone F)
(Z : D)
(z : Hom ((F k) X) Z)
 : ((Y.cone_maps j).components X) ≫ ((F &> f).components X) ≫ z = (Y.cone_maps k).components X ≫ z := 
begin
 rw ← category.associativity,
 simp
end

@[simp] lemma cone_morphism_commutativity_in_FunctorCategory
(F : Functor J (Functor C D))
(X : C)
(j : J)
(Y Z : Cone F)
(φ : ConeMorphism Y Z)
 : ((φ.cone_morphism).components X) ≫ ((Z.cone_maps j).components X) = (Y.cone_maps j).components X := 
begin
  have p := φ.commutativity j,
  have p' := congr_arg NaturalTransformation.components p,
  exact congr_fun p' X,
end


end categories.universal.lemmas.cones_in_functor_categories
