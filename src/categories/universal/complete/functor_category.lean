-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..complete

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.isomorphism
open categories.initial

namespace categories.universal

universes j u₁ u₂
section
variable {J : Type (j+1)}
variable [category J]
variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

@[reducible] private definition evaluate_Functor_to_FunctorCategory (F : Functor J (Functor C D)) (c : C) : Functor J D := {
  onObjects     := λ j, (F.onObjects j).onObjects c,
  onMorphisms   := λ _ _ f, (F.onMorphisms f).components c
}

@[reducible] private definition evaluate_Functor_to_FunctorCategory_on_Morphism (F : Functor J (Functor C D)) {c c' : C} (f : Hom c c')
  : NaturalTransformation (evaluate_Functor_to_FunctorCategory F c) (evaluate_Functor_to_FunctorCategory F c') := {
    components := λ j, (F.onObjects j).onMorphisms f
 }

-- PROJECT do this properly, as
-- private definition Switch_Curry : Functor (Functor J (Functor C D)) (Functor C (Functor J D)) := 
end

section
variable {J : Type (u₁+1)}
variable [category J]
variable {C : Type (u₁+2)}
variable [category C]
variable {D : Type (u₁+2)}
variable [category D]

private definition LimitObject_in_FunctorCategory [cmp : Complete D] (F : Functor J (Functor C D)) : Cone F := {     
  cone_point    := {
    onObjects     := λ c, functorial_Limit.onObjects (evaluate_Functor_to_FunctorCategory F c),
    onMorphisms   := λ _ _ f, functorial_Limit.onMorphisms (evaluate_Functor_to_FunctorCategory_on_Morphism F f),
 },
  cone_maps     := λ j, {
    components := λ c, (limitCone (evaluate_Functor_to_FunctorCategory F c)).terminal_object.cone_maps j,
 },
}

@[applicable] lemma uniqueness_of_morphisms_to_terminal_object_cone_point 
  {Z : D}
  {G : Functor J D}
  {L : LimitCone G}
  (cone_maps : Π j : J, Hom Z (G.onObjects j)) 
  (commutativity : Π j k : J, Π f : Hom j k, (cone_maps j) ≫ (G.onMorphisms f) = cone_maps k)
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
  : ((F.onObjects j).onMorphisms f) ≫ ((F.onMorphisms g).components Y)
  = ((F.onMorphisms g).components X) ≫ ((F.onObjects k).onMorphisms f) := ♯

@[simp] lemma cone_in_functor_category 
(F : Functor J (Functor C D))
(X Y : C)
(f : Hom X Y)
(j k : J)
(g : Hom j k)
(cone : Cone F)
: ((cone.cone_maps j).components X) ≫ ((F.onObjects j).onMorphisms f) ≫ 
      ((F.onMorphisms g).components Y) =
    ((cone.cone_maps k).components X) ≫ ((F.onObjects k).onMorphisms f) :=
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
  : ((cone.cone_point).onMorphisms f) ≫ ((cone.cone_maps j).components Y) =
    ((cone.cone_maps j).components X) ≫ ((F.onObjects j).onMorphisms f) := ♯

@[simp] lemma cone_commutativity_in_FunctorCategory
(F : Functor J (Functor C D))
(X : C)
(j k : J)
(f : Hom j k) 
(Y : Cone F)
 : ((Y.cone_maps j).components X) ≫ ((F.onMorphisms f).components X) = (Y.cone_maps k).components X := 
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
(z : Hom ((F.onObjects k).onObjects X) Z)
 : ((Y.cone_maps j).components X) ≫ ((F.onMorphisms f).components X) ≫ z = (Y.cone_maps k).components X ≫ z := 
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

-- needed for the proof of naturality below
local attribute [reducible] universal.lemmas.limit_functoriality.morphism_to_terminal_object_cone_point

private definition morphism_to_LimitObject_in_FunctorCategory [cmp : Complete D] {F : Functor J (Functor C D)} (Y : Cone F) : ConeMorphism Y (LimitObject_in_FunctorCategory F) := {
      cone_morphism := {
        components := begin
                         tidy {hints:=[7, 6, 7, 9, 23, 25]},  -- this will use morphism_to_terminal_object_cone_point
                         exact (Y.cone_maps j).components X, 
                         exact congr_fun (congr_arg (NaturalTransformation.components) (Y.commutativity f)) X,  
                       end,
        naturality := begin tidy {hints:=[9, 7, 6, 7, 9, 23, 19, 9, 10, 9, 10]}, end
     },
      commutativity := by tidy {hints:=[9, 7, 6, 7, 9, 10]} 
   }

-- This would be a bit dangerous, but we just use it in the next construction.
@[applicable] private lemma cone_morphism_comparison
(F : Functor J (Functor C D))
(X : C)
(j : J)
(Y Z : Cone F)
(φ φ' : ConeMorphism Y Z)
(f : Hom ((Z.cone_point).onObjects X) ((F.onObjects j).onObjects X))
(w : f = ((Z.cone_maps j).components X))
 : ((φ.cone_morphism).components X) ≫ f = ((φ'.cone_morphism).components X) ≫ f := 
begin
  rewrite w,
  simp,
end

instance Limits_in_FunctorCategory [cmp : Complete D] : Complete (Functor C D) := {
  limitCone := λ J _ F, 
  begin
  resetI,
  exact {
    terminal_object                            := @LimitObject_in_FunctorCategory J _ C _ _ _ _ F,
    morphism_to_terminal_object_from           := λ Y, morphism_to_LimitObject_in_FunctorCategory Y
 }
 end
}

end
end categories.universal