-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .isomorphism
import .opposites
import .equivalence
import .products.products
import .examples.types.types

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.equivalence
open tqft.categories.examples.types
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

-- PROJECT
-- How do we even get the universes to work?
-- theorem {u v} WeakYonedaLemma ( C : Category.{u v} ) ( X : C.Obj ) ( F : Functor (Opposite C) (CategoryOfTypes) ) :
--   Isomorphism CategoryOfTypes (NaturalTransformation (Yoneda C X) F) (F X) :=
--   sorry

-- PROJECT set up the Yoneda lemma as a natural isomorphism
-- definition {u v} Evaluation ( C : Category.{u v} ) : Functor (ProductCategory (FunctorCategory (Opposite C) CategoryOfTypes.{v}) (Opposite C)) CategoryOfTypes.{v} :=
-- {
--     onObjects     := λ p, (p.1.onObjects p.2),
--     onMorphisms   := λ x y f, (f.1.components y.2) ∘ (x.1.onMorphisms f.2),
--     identities    := begin blast, erewrite Functor.identities, blast end,
--     functoriality := begin
--                       intros X Y Z,
--                       induction X with X1 X2,
--                       induction Y with Y1 Y2,
--                       induction Z with Z1 Z2,
--                       intros f g,
--                       induction f with f1 f2,
--                       induction g with g1 g2,
--                       unfold_unfoldable,
--                       blast,
--                       apply congr_arg,
--                       erewrite X1.functoriality,
--                       unfold_unfoldable,                      
--                       admit,
--                     end
-- } 

-- definition {u v} Pairing ( C : Category.{u v} ) : Functor (ProductCategory (FunctorCategory (Opposite C) CategoryOfTypes.{v}) (Opposite C)) CategoryOfTypes.{max u v} :=
-- {
--     onObjects     := λ p, NaturalTransformation p.1 (Yoneda C p.2),
--     onMorphisms   := λ x y f, sorry,
--     identities    := sorry,
--     functoriality := sorry
-- }

-- theorem {u v} YonedaLemma ( C : Category.{u v} ) : NaturalIsomorphism (Pairing C) (Evaluation C) := sorry

private lemma {u v w} composition {α : Sort u} {β : Sort v} {γ : Sort w} {f : α → β} {g : β → γ} (a : α) : (g ∘ f) a = g (f a) := ♯

theorem {u v} YonedaEmbedding ( C : Category.{u v} ) : Embedding (Yoneda C) :=
begin
  blast,
  {
    -- Show it is full
    fsplit,
    {
        intros,
        exact (f.components X) (C.identity X)
    },
    {
        blast,
        pose p := f.naturality x,
        simp at p,
        unfold CategoryOfTypes at p,
        simp at p,
        pose q := congr_fun p (C.identity X),
        rewrite composition at q,
        rewrite C.right_identity at q,
        exact (eq.symm q)
    }
  },
  {
    -- Show it is faithful
    fsplit,
    unfold_unfoldable,
    intros,
    pose q := congr_arg NaturalTransformation.components p,
    simp at q,
    pose q' := congr_fun q X,
    simp at q',
    pose q'' := congr_fun q' (C.identity X),
    simp at q'',
    exact q''
  }
end

end tqft.categories.yoneda