-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .isomorphism
import .opposites
import .equivalence
import .products.products
import .products.switch
import .types

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.equivalence
open tqft.categories.types
open tqft.categories.products

namespace tqft.categories.yoneda

definition {u v} Yoneda ( C : Category.{u v} ) : Functor C (FunctorCategory (Opposite C) CategoryOfTypes.{v}) :=
{
    onObjects := λ X, {
        onObjects     := λ Y, C.Hom Y X,
        onMorphisms   := λ Y Y' f, λ g, C.compose f g,
        identities    := ♯,
        functoriality := ♯ 
    },
    onMorphisms   := λ X X' f, {
        components := λ Y, λ g, C.compose g f,
        naturality := ♯
    },
    identities    := ♯,
    functoriality := ♯
}

@[reducible] definition {v} YonedaEvaluation ( C : Category.{v v} )
  : Functor (ProductCategory (FunctorCategory (Opposite C) CategoryOfTypes.{v}) (Opposite C)) CategoryOfTypes.{v}
  := Evaluation (Opposite C) CategoryOfTypes.{v}
@[reducible] definition {v} YonedaPairing ( C : Category.{v v} ) 
  : Functor (ProductCategory (FunctorCategory (Opposite C) CategoryOfTypes.{v}) (Opposite C)) CategoryOfTypes.{v}
  := FunctorComposition
      (FunctorComposition
        (ProductFunctor (IdentityFunctor _) (OppositeFunctor (Yoneda C)))
        (SwitchProductCategory _ _))
      (HomPairing (FunctorCategory (Opposite C) CategoryOfTypes.{v})) 

private lemma YonedaLemma_aux_1
   { C : Category }
   { X Y : C.Obj }
   ( f : C.Hom X Y )
   { F G : Functor (Opposite C) CategoryOfTypes }
   ( τ : NaturalTransformation F G )
   ( Z : F.onObjects Y ) :
     G.onMorphisms f (τ.components Y Z) = τ.components X (F.onMorphisms f Z) := eq.symm (congr_fun (τ.naturality f) Z)


private lemma YonedaLemma_aux_2
   { C : Category }
   { X Y : C.Obj }
   ( f : C.Hom X Y )
   { F : Functor (Opposite C) CategoryOfTypes }
   ( τ : NaturalTransformation (Yoneda C Y) F ) :
     F.onMorphisms f (τ.components Y (C.identity Y)) = τ.components X f :=
begin
 note p := eq.symm (congr_fun (τ.naturality f) (C.identity Y)),
 tidy,
 exact p
end


-- PROJECT think about how to write a saner proof.
theorem {v} YonedaLemma ( C : Category.{v v} ) : NaturalIsomorphism (YonedaPairing C) (YonedaEvaluation C) := --sorry
begin
  unfold NaturalIsomorphism,
  fsplit,
  {
    unfold FunctorCategory,
    dsimp,
    fsplit,
    {
      tidy,
      exact ((a.components _) (C.identity _))
    },
    {
      tidy,
      note q := congr_fun (x.naturality snd_2) (C.identity snd_1),
      tidy,
      rewrite q,
    }
  },
  {
    unfold FunctorCategory,
    dsimp,
    fsplit,
    {
      tidy,
      exact ((fst.onMorphisms a_1) a),
      tidy,
      erewrite Functor.functoriality, -- FIXME why does this require erewrite?
      tidy,
    },
    {
      tidy,
      erewrite Functor.functoriality, -- FIXME why does this require erewrite?
      tidy,
      rewrite YonedaLemma_aux_1,      
    }
  },
  {
    tidy,
    rewrite YonedaLemma_aux_2,      
  },
  {
    tidy,
    erewrite Functor.identities, -- FIXME why does this require erewrite?
    tidy,
  }
end


theorem {u v} YonedaEmbedding ( C : Category.{u v} ) : Embedding (Yoneda C) :=
begin
  unfold Embedding,
  fsplit,
  {
    -- Show it is full
    fsplit,
    {
        tidy,
        exact (f.components X) (C.identity X)
    },
    {
        tidy,
        note p := f.naturality x,
        tidy,
        note q := congr_fun p (C.identity X),
        blast
    }
  },
  {
    -- Show it is faithful
    fsplit,
    tidy,
    note q := congr_arg NaturalTransformation.components p,
    note q' := congr_fun q X,
    note q'' := congr_fun q' (C.identity X),
    blast
  }
end

end tqft.categories.yoneda