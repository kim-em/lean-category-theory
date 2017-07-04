-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..complete
import ...walking

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.initial
open categories.walking
open categories.util.finite

namespace categories.universal

private definition {u v} Cone_from_map_to_limit
  { C : Category.{u v} }
  { J : Category.{u v} } 
  { F : Functor J C } 
  { L : LimitCone F } 
  { Z : C.Obj } 
  ( f : C.Hom Z L.terminal_object.cone_point ) : Cone F :=
{
  cone_point    := Z,
  cone_maps     := λ j, C.compose f (L.terminal_object.cone_maps j),
  commutativity := ♯ 
}
private definition {u v} ConeMorphism_from_map_to_limit
  { C : Category.{u v} }
  { J : Category.{u v} } 
  { F : Functor J C } 
  { L : LimitCone F } 
  { Z : C.Obj } 
  ( f : C.Hom Z L.terminal_object.cone_point ) : ConeMorphism (Cone_from_map_to_limit f) L.terminal_object :=
{
  cone_morphism      := f,
  commutativity := ♯ 
}

open categories.util.finite.Two

-- This is a useless mess. We better make the walking parallel pair explicit, rather than a path category on the corresponding graph.
-- instance Equalizers_from_Limits ( C : Category ) [ Complete C ] : has_Equalizers C := {
--   equalizer := λ X Y f g, let lim := limitCone(ParallelPair_functor f g) in {
--     equalizer     := lim.terminal_object.cone_point,
--     inclusion     := lim.terminal_object.cone_maps _0,
--     witness       := let commutativity := @Cone.commutativity _ _ _ lim.terminal_object _0 _1 in 
--                      begin
--                        have fw := commutativity (@path.cons WalkingParallelPair _0 _1 _1 _0 (@path.nil WalkingParallelPair _1)),
--                        have gw := commutativity (@path.cons WalkingParallelPair _0 _1 _1 _1 (@path.nil WalkingParallelPair _1)),
--                        tidy,
--                        unfold path_to_morphism at fw, 
--                        unfold ParallelPair_functor at fw, 
--                        unfold ParallelPair_homomorphism at fw, 
--                        tidy,
--                        unfold path_to_morphism at gw, 
--                      end,
--     map           := sorry,
--     factorisation := sorry,
--     uniqueness    := sorry
--   }                       
-- }

instance Products_from_Limits ( C : Category ) [ Complete C ] : has_Products C := {
    product := λ { I : Type } ( F : I → C.Obj ), 
                 let lim_F := limitCone (Functor.fromFunction F) in
                  {
                    product       := lim_F.terminal_object.cone_point,
                    projection    := λ i, lim_F.terminal_object.cone_maps i,
                    uniqueness    := λ Z f g, begin
                                                intros, 
                                                have p := lim_F.uniqueness_of_morphisms_to_terminal_object, 
                                                have q := p _ (ConeMorphism_from_map_to_limit f)
                                                  { cone_morphism := g, commutativity := begin tidy, exact eq.symm (witness j) end },
                                                exact congr_arg ConeMorphism.cone_morphism q, -- surely this line can be automated: if you know a = b, you know a.x = b.x
                                              end,
                    map           := λ Z i, (lim_F.morphism_to_terminal_object_from { cone_point := Z, cone_maps := i, commutativity := ♯ }).cone_morphism,
                    factorisation := ♯ 
                  }
}

instance Limits_from_Products_and_Equalizers ( C : Category ) [ has_Products C ] [ has_Equalizers C ] : Complete C := {
  limitCone := λ J F,
    let product_over_objects   := product (F.onObjects) in
    let product_over_morphisms := product (λ f : ( Σ s : J.Obj, Σ t : J.Obj, J.Hom s t ), F.onObjects f.2.1) in
    let source    := product_over_morphisms.map (λ f, C.compose (product_over_objects.projection f.1) (F.onMorphisms f.2.2) )  in
    let target    := product_over_morphisms.map (λ f, product_over_objects.projection f.2.1 ) in
    let source_projection_lemma : ∀ t : ( Σ s : J.Obj, Σ t : J.Obj, J.Hom s t ), C.compose source (product_over_morphisms.projection t) = C.compose (product_over_objects.projection t.1) (F.onMorphisms t.2.2) := ♯ in
    let target_projection_lemma : ∀ t : ( Σ s : J.Obj, Σ t : J.Obj, J.Hom s t ), C.compose target (product_over_morphisms.projection t) = product_over_objects.projection t.2.1 := ♯ in
    let equalizer := equalizer source target in {
      terminal_object     := {
        cone_point    := equalizer.equalizer,
        cone_maps     := λ j : J.Obj, C.compose equalizer.inclusion (product_over_objects.projection j),
        commutativity := λ j k f, begin
                                   -- PROJECT learn how to use calc!
                                   have p := congr_arg (λ i, C.compose i (product_over_morphisms.projection ⟨ j, ⟨ k, f ⟩ ⟩)) equalizer.witness,
                                  --  simp at p,
                                  --  repeat_at_least_once { rewrite C.associativity at p },
                                   blast,                                   
                                  end
      },
      morphism_to_terminal_object_from := λ cone : Cone F, {
        cone_morphism      := /- we need a morphism from the tip of f to the equalizer -/
                         equalizer.map
                           (product_over_objects.map cone.cone_maps)
                           /- we need to provide the evidence that that map composes correctly with source and target -/
                           begin
                            -- blast should work from the beginning here, but takes longer than I have patience for
                            --  pointwise,
                            --  intros,
                            --  repeat_at_least_once { rewrite C.associativity },
                             blast,
                           end,
        commutativity := /- we need to show that that map commutes with everything -/
          begin
            intros, 
            rewrite - C.associativity,
            tidy,
          end
      },
      uniqueness_of_morphisms_to_terminal_object := λ cone f g, begin
                                  -- tidy, 
                                  -- repeat_at_least_once { rewrite C.associativity }, -- unfortunately blast doesn't work here
                                  tidy,
                                end
    }
}

end categories.universal