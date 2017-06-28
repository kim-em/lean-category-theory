-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .universal

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.initial
open tqft.categories.types
open tqft.categories.util

namespace tqft.categories.universal

class Complete ( C : Category ) := 
  ( limit : Π { J : Category } ( F : Functor J C ), Limit F )

-- FIXME why on earth doesn't this work?
-- definition limit { C : Category } [ Complete C ] { J : Category } ( F : Functor J C ) := Complete.limit F

-- TODO might be easiest to first do Product and comma.Product comparison
-- instance Products_from_Limits ( C : Category ) [ Complete C ] : has_Products C := {
--     product := 
-- }

private definition evaluate_Functor_to_FunctorCategory { J C D : Category } ( F : Functor J (FunctorCategory C D )) ( c : C.Obj ) : Functor J D := {
  onObjects     := λ j, (F.onObjects j).onObjects c,
  onMorphisms   := λ _ _ f, (F.onMorphisms f).components c,
  identities    := ♯,
  functoriality := ♯ 
}

private definition evaluate_Functor_to_FunctorCategory_on_Morphism { J C D : Category } ( F : Functor J (FunctorCategory C D )) ( c c' : C.Obj ) ( f : C.Hom c c' )
  : NaturalTransformation (evaluate_Functor_to_FunctorCategory F c) (evaluate_Functor_to_FunctorCategory F c') := {
    components := λ j, (F.onObjects j).onMorphisms f,
    naturality := ♯ 
  }

-- PROJECT
-- instance Limits_in_FunctorCategory ( C D : Category ) [ cmp : Complete D ] : Complete (FunctorCategory C D) := {
--   limit := λ J F, {
--     object     := {
--       -- TODO the whole definition of limit should come down to the fact that limits are functorial
--       limit         := {
--         -- See the FIXME above: why all the boilerplate here?
--         onObjects     := λ c, (@Complete.limit D cmp J (evaluate_Functor_to_FunctorCategory F c)).object.limit,
--         onMorphisms   := λ c c' f, sorry,
--         identities    := sorry,
--         functoriality := sorry
--       },
--       maps          := sorry,
--       commutativity := sorry
--     },
--     morphisms  := sorry,
--     uniqueness := sorry
--   }
-- }

instance Limits_from_Products_and_Equalizers ( C : Category ) [ has_Products C ] [ has_Equalizers C ] : Complete C := {
  limit := λ J F,
    let product_over_objects   := product (F.onObjects) in
    let product_over_morphisms := product (λ f : ( Σ s : J.Obj, Σ t : J.Obj, J.Hom s t ), F.onObjects f.2.1) in
    let source    := product_over_morphisms.map (λ f, C.compose (product_over_objects.projection f.1) (F.onMorphisms f.2.2) )  in
    let target    := product_over_morphisms.map (λ f, product_over_objects.projection f.2.1 ) in
    let source_projection_lemma : ∀ t : ( Σ s : J.Obj, Σ t : J.Obj, J.Hom s t ), C.compose source (product_over_morphisms.projection t) = C.compose (product_over_objects.projection t.1) (F.onMorphisms t.2.2) := ♯ in
    let target_projection_lemma : ∀ t : ( Σ s : J.Obj, Σ t : J.Obj, J.Hom s t ), C.compose target (product_over_morphisms.projection t) = product_over_objects.projection t.2.1 := ♯ in
    let equalizer := equalizer source target in {
      object     := {
        limit         := equalizer.equalizer,
        maps          := λ j : J.Obj, C.compose equalizer.inclusion (product_over_objects.projection j),
        commutativity := λ j k f, begin
                                   -- PROJECT learn how to use have, show, and calc!
                                   have p := congr_arg (λ i, C.compose i (product_over_morphisms.projection ⟨ j, ⟨ k, f ⟩ ⟩)) equalizer.witness,
                                   simp at p,
                                   repeat { rewrite C.associativity at p },
                                   rewrite [ source_projection_lemma, target_projection_lemma ] at p,
                                   rewrite - C.associativity at p,
                                   exact p,
                                  end
      },
      morphisms  := λ cone : Cone F, {
        morphism      := /- we need a morphism from the tip of f to the equalizer -/
                         equalizer.map
                           (product_over_objects.map cone.maps)
                           /- we need to provide the evidence that that map composes correctly with source and target -/
                           begin
                             pointwise,
                             intros,
                             repeat { rewrite C.associativity },
                             rewrite [ source_projection_lemma, target_projection_lemma ],
                             rewrite - C.associativity,
                             repeat { rewrite product_over_objects.factorisation },
                             rewrite cone.commutativity,
                           end,
        commutativity := /- we need to show that that map commutes with everything -/
          begin
            intros,
            rewrite - C.associativity,
            simp,
          end
      },
      uniqueness := λ cone f g, begin
                                  pointwise,
                                  pointwise,
                                  pointwise,
                                  intros,
                                  have u := f.commutativity i,
                                  have v := g.commutativity i,
                                  unfold_projections_hypotheses,
                                  repeat { rewrite C.associativity },
                                  rewrite [ u, v ],
                                end
    }
}

end tqft.categories.universal