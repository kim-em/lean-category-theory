-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..complete
import ..opposites
import ...walking
import tidy.its

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.initial
open categories.walking
open categories.util.finite
open categories.universal.opposites

namespace categories.universal

universes u₁ u₂ u₃ u₄

private definition Cone_from_map_to_limit
  { C : Category }
  { J : Category } 
  { F : Functor J C } 
  { L : LimitCone F } 
  { Z : C.Obj } 
  ( f : C.Hom Z L.terminal_object.cone_point ) : Cone F :=
{
  cone_point    := Z,
  cone_maps     := λ j, C.compose f (L.terminal_object.cone_maps j)
}
private definition ConeMorphism_from_map_to_limit
  { C : Category }
  { J : Category } 
  { F : Functor J C } 
  { L : LimitCone F } 
  { Z : C.Obj } 
  ( f : C.Hom Z L.terminal_object.cone_point ) : ConeMorphism (Cone_from_map_to_limit f) L.terminal_object :=
{
  cone_morphism := f
}

set_option pp.universes true
set_option trace.class_instances true

open categories.util.finite.Two

-- PROJECT this construction is unpleasant
definition Equalizers_from_Limits ( C : Category.{u₁ u₂} ) [ Complete.{u₁ u₂ 0 0} C ] : has_Equalizers.{u₁ u₂} C := {
  equalizer := λ X Y f g, let lim := limitCone(ParallelPair_functor f g) in {
    equalizer     := lim.terminal_object.cone_point,
    inclusion     := lim.terminal_object.cone_maps Two._0,
    witness       := let commutativity := @Cone.commutativity_lemma _ _ _ lim.terminal_object Two._0 Two._1 in 
                     begin
                       dsimp,
                       erw commutativity tt,
                       erw commutativity ff,
                     end,
    map           := begin
                       -- PROJECT this is really ugly! Those inductions should work better...
                       tidy,
                       induction j,
                       tidy,
                       exact k,
                       exact C.compose k f,
                       induction j,
                       induction k_1,
                       tidy,
                       induction f_1,
                       tidy,
                       induction k_1,
                       tidy,
                       induction f_1,
                       induction f_1,
                       tidy,
                     end,
    factorisation := begin
                       tidy,
                       unfold universal.morphism_to_terminal_object_cone_point,
                       tidy,
                     end,
    uniqueness    := begin
                       tidy,
                       let Z_cone : Cone (ParallelPair_functor f g) := {
                         cone_point := Z,
                         cone_maps := λ j : Two, C.compose a (lim.terminal_object.cone_maps j),
                         commutativity := begin
                                            tidy, any_goals { induction f_1 }, tidy,
                                            {
                                              have c := lim.terminal_object.commutativity,
                                              erw @c Two._0 Two._1 ff,
                                            },
                                            {
                                              have c := lim.terminal_object.commutativity,
                                              erw @c Two._0 Two._1 tt,
                                            },
                                          end
                       },
                       have p := lim.uniqueness_of_morphisms_to_terminal_object Z_cone ⟨ a, _ ⟩ ⟨ b, _ ⟩,
                       exact congr_arg ConeMorphism.cone_morphism p,
                       -- finally, take care of those placeholders
                       tidy,
                       have c := lim.terminal_object.commutativity,
                       rw ← @c Two._0 Two._1 tt,
                       repeat { rw ← C.associativity },
                       rw witness, 
                     end
  }                       
}

definition Products_from_Limits (C : Category.{u₁ u₂}) [Complete.{u₁ u₂ u₃ u₄} C] : has_Products.{u₁ u₂ u₃} C := {
    product := λ {I : Type u₃} (F : I → C.Obj), 
                 let lim_F := limitCone (Functor.fromFunction F) in
                  {
                    product       := lim_F.terminal_object.cone_point,
                    projection    := λ i, lim_F.terminal_object.cone_maps i,
                    uniqueness    := λ Z f g, begin
                                                intros, 
                                                have p := lim_F.uniqueness_of_morphisms_to_terminal_object, 
                                                have q := p _ (ConeMorphism_from_map_to_limit f)
                                                  { cone_morphism := g, commutativity := begin tidy, simp *, end }, -- PROJECT think about automation here
                                                exact congr_arg ConeMorphism.cone_morphism q, -- PROJECT surely this line can be automated: if you know a = b, you know a.x = b.x
                                              end,
                    map           := λ Z i, (lim_F.morphism_to_terminal_object_from { 
                                              cone_point := Z, 
                                              cone_maps := i, 
                                              commutativity := ♯ 
                                            }).cone_morphism,
                    factorisation := ♯ 
                  }
}

instance Limits_from_Products_and_Equalizers ( C : Category.{u₁ u₂} ) [ has_Products.{u₁ u₂ u₃} C ] [ has_Equalizers.{u₁ u₂} C ] : Complete.{u₁ u₂ u₃ u₃} C := {
  limitCone := λ J F,
    let product_over_objects   := product (F.onObjects) in
    let product_over_morphisms := product (λ f : ( Σ s : J.Obj, Σ t : J.Obj, J.Hom s t ), F.onObjects f.2.1) in
    let source    := product_over_morphisms.map (λ f, C.compose (product_over_objects.projection f.1) (F.onMorphisms f.2.2) )  in
    let target    := product_over_morphisms.map (λ f, product_over_objects.projection f.2.1 ) in
    let equalizer := equalizer source target in {
      terminal_object     := {
        cone_point    := equalizer.equalizer,
        cone_maps     := λ j : J.Obj, C.compose equalizer.inclusion (product_over_objects.projection j),
        commutativity := λ j k f, begin
                                   have p := congr_arg (λ i, C.compose i (product_over_morphisms.projection ⟨ j, ⟨ k, f ⟩ ⟩)) equalizer.witness,                                
                                   tidy,
                                  end
      },
      morphism_to_terminal_object_from := λ cone : Cone F, {
        cone_morphism := /- we need a morphism from the tip of f to the equalizer -/
                         equalizer.map
                           (product_over_objects.map cone.cone_maps) ♯
      }
    }
}

open categories.opposites


instance Coequalizers_from_Colimits ( C : Category.{u₁ u₂} ) [ Cocomplete.{u₁ u₂ u₃ u₄} C ] : has_Coequalizers.{u₁ u₂} C := {
  coequalizer := λ _ _ f g, Equalizer_in_Opposite (@equalizer (Opposite C) _ _ _ f g)
}

instance Coproducts_from_Colimits ( C : Category.{u₁ u₂} ) [ Cocomplete.{u₁ u₂ u₃ u₄} C ] : has_Coproducts.{u₁ u₂ u₃} C := {
  coproduct := λ _ F, Product_in_Opposite (@product (Opposite C) _ _ F)
}

instance Colimits_from_Coproducts_and_Coequalizers ( C : Category.{u₁ u₂} ) [ has_Coproducts.{u₁ u₂ u₃} C ] [ has_Coequalizers.{u₁ u₂} C ] : Cocomplete.{u₁ u₂ u₃ u₃} C := sorry


end categories.universal