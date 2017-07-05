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

@[reducible] private definition evaluate_Functor_to_FunctorCategory { J C D : Category } ( F : Functor J (FunctorCategory C D )) ( c : C.Obj ) : Functor J D := {
  onObjects     := λ j, (F.onObjects j).onObjects c,
  onMorphisms   := λ _ _ f, (F.onMorphisms f).components c,
  identities    := ♯,
  functoriality := ♯ 
}

@[reducible] private definition evaluate_Functor_to_FunctorCategory_on_Morphism { J C D : Category } ( F : Functor J (FunctorCategory C D )) { c c' : C.Obj } ( f : C.Hom c c' )
  : NaturalTransformation (evaluate_Functor_to_FunctorCategory F c) (evaluate_Functor_to_FunctorCategory F c') := {
    components := λ j, (F.onObjects j).onMorphisms f,
    naturality := ♯ 
  }

-- private definition switch { J C D : Category } : Functor (FunctorCategory J (FunctorCategory C D)) (FunctorCategory C (FunctorCategory J D)) :=
--   FunctorComposition (FunctorComposition (Uncurry_Functors J C D) (whisker_on_left_functor _ (SwitchProductCategory C J))) (Curry_Functors C J D)

private definition LimitObject_in_FunctorCategory { J C D : Category } [ cmp : Complete D ] ( F : Functor J (FunctorCategory C D) ) : Cone F := {      
  cone_point    := -- FunctorComposition (switch.onObjects F) Limit, -- this is a fancy alternative, but I get stuck following through.
  {
    onObjects     := λ c, Limit.onObjects (evaluate_Functor_to_FunctorCategory F c),
    onMorphisms   := λ _ _ f, Limit.onMorphisms (evaluate_Functor_to_FunctorCategory_on_Morphism F f),
    identities    := ♯,
    functoriality := begin tidy, /-rewrite D.associativity, simp, -/rewrite ← D.associativity, simp,/- rewrite D.associativity-/ end
  },
  cone_maps     := λ j, {
    components := λ c, (limitCone (evaluate_Functor_to_FunctorCategory F c)).terminal_object.cone_maps j,
    naturality := ♯ 
  },
  commutativity := ♯ 
}

@[applicable] lemma uniqueness_of_morphisms_to_terminal_object_cone_point 
  { J D : Category }
  { Z : D.Obj }
  { G : Functor J D }
  { L : LimitCone G }
  ( cone_maps : Π j : J.Obj, D.Hom Z (G.onObjects j) ) 
  ( commutativity : Π j k : J.Obj, Π f : J.Hom j k, D.compose (cone_maps j) (G.onMorphisms f) = cone_maps k )
  ( f g : D.Hom Z L.terminal_object.cone_point )
  ( commutativity_f : Π j : J.Obj, D.compose f (L.terminal_object.cone_maps j) = cone_maps j )
  ( commutativity_g : Π j : J.Obj, D.compose g (L.terminal_object.cone_maps j) = cone_maps j )
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

-- IDEAS:
-- suppress pretty printing of irrelevant properties
-- extract a goal as a lemma
-- on rename of Lean file, delete olean file
-- warn on unused imports (even unused opens?)

lemma bifunctor_naturality  
( J C D : Category )
( F : Functor J (FunctorCategory C D) )
( X Y : C.Obj )
( f : C.Hom X Y )
( j k : J.Obj )
( g : J.Hom j k )
  : D.compose ((F.onObjects j).onMorphisms f) ((F.onMorphisms g).components Y)
  = D.compose ((F.onMorphisms g).components X) ((F.onObjects k).onMorphisms f) := ♯

@[simp] lemma cone_in_functor_category 
( J C D : Category )
( F : Functor J (FunctorCategory C D) )
( X Y : C.Obj )
( f : C.Hom X Y )
( j k : J.Obj )
( g : J.Hom j k )
( cone : Cone F )
: D.compose (D.compose ((cone.cone_maps j).components X) ((F.onObjects j).onMorphisms f))
      ((F.onMorphisms g).components Y) =
    D.compose ((cone.cone_maps k).components X) ((F.onObjects k).onMorphisms f) :=
begin
  have p := cone.commutativity g,
  have p' := congr_arg NaturalTransformation.components p,
  have p'' := congr_fun p' X,
  tidy,
  -- rewrite D.associativity,
  rewrite bifunctor_naturality,
  rewrite ← D.associativity,
  rewrite p'',
end

@[simp] lemma cone_in_functor_category_naturality
( J C D : Category )
( F : Functor J (FunctorCategory C D) )
( X Y : C.Obj )
( f : C.Hom X Y )
( j : J.Obj )
( cone : universal.Cone F )
  : D.compose ((cone.cone_point).onMorphisms f) ((cone.cone_maps j).components Y) =
    D.compose ((cone.cone_maps j).components X) ((F.onObjects j).onMorphisms f) := ♯

private definition morphism_to_LimitObject_in_FunctorCategory { J C D : Category } [ cmp : Complete D ] { F : Functor J (FunctorCategory C D) } ( Y : Cone F ) : ConeMorphism Y (LimitObject_in_FunctorCategory F) := {
      cone_morphism := {
        components := begin
                         tidy,  -- this will use morphism_to_terminal_object_cone_point
                         exact (Y.cone_maps j).components X, 
                         tidy, 
                         exact congr_fun (congr_arg (NaturalTransformation.components) (Y.commutativity f)) X,                       
                       end,
        naturality := begin 
                        tidy,
                        exact D.compose ((Y.cone_maps j).components X) ((F.onObjects j).onMorphisms f),
                        tidy, -- uses cone_in_functor_category
                        unfold morphism_to_terminal_object_cone_point,
                        tidy,
                        -- rewrite D.associativity,
                        -- tidy,
                        unfold morphism_to_terminal_object_cone_point,
                        tidy,
                        -- rewrite D.associativity,
                        -- tidy,
                        rewrite ← D.associativity,
                        tidy,
                      end
      },
      commutativity := begin
                         tidy, 
                         unfold morphism_to_terminal_object_cone_point,
                         tidy,
                       end
    }

lemma Y : 1 = 1 := ♯

@[simp] lemma cone_commutativity_in_FunctorCategory
( J C D  : Category )
( F : Functor J (FunctorCategory C D) )
( X : C.Obj )
( j k : J.Obj )
( f : J.Hom j k ) 
( Y : Cone F )
 : D.compose ((Y.cone_maps j).components X) ((F.onMorphisms f).components X) = (Y.cone_maps k).components X := 
begin
 have p := Y.commutativity f,
 have p' := congr_arg NaturalTransformation.components p,
 tidy,
end

@[applicable] lemma cone_morphism_commutativity_with_unknown_in_FunctorCategory
( J C D  : Category )
( F : Functor J (FunctorCategory C D) )
( X : C.Obj )
( j : J.Obj )
( Y Z : Cone F )
( φ : ConeMorphism Y Z )
( f : D.Hom ((Z.cone_point).onObjects X) ((F.onObjects j).onObjects X) )
( w : f = ((Z.cone_maps j).components X) )
 : D.compose ((φ.cone_morphism).components X) f = (Y.cone_maps j).components X:= 
begin
  have p := φ.commutativity j,
  have p' := congr_arg NaturalTransformation.components p,
  have p'' := congr_fun p' X,
  tidy,
  rewrite w,
  exact p''
end

instance Limits_in_FunctorCategory ( C D : Category ) [ cmp : Complete D ] : Complete (FunctorCategory C D) := {
  limitCone := λ J F, {
    terminal_object                            := LimitObject_in_FunctorCategory F,
    morphism_to_terminal_object_from           := λ Y, morphism_to_LimitObject_in_FunctorCategory Y,
    uniqueness_of_morphisms_to_terminal_object := begin 
                                                    tidy, 
                                                    exact (Y.cone_maps j).components X, 
                                                    tidy
                                                  end
  }
}

end categories.universal