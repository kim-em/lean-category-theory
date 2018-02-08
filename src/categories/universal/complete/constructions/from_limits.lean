-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ...complete
import ...opposites
import categories.walking
import tidy.its

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.initial
open categories.walking
open categories.util.finite

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

-- PROJECT this construction is unpleasant
instance Equalizers_from_Limits ( C : Category.{u₁ u₂} ) [ Complete.{u₁ u₂ 0 0} C ] : has_Equalizers.{u₁ u₂} C := {
  equalizer := λ X Y f g, let lim := limitCone(ParallelPair_functor f g) in {
    equalizer     := lim.terminal_object.cone_point,
    inclusion     := lim.terminal_object.cone_maps Two._0,
    witness       := let commutativity := @Cone.commutativity_lemma _ _ _ lim.terminal_object Two._0 Two._1 in 
                     begin
                       dsimp,
                       erw commutativity Two._0,
                       erw commutativity Two._1,
                     end,
    map           := begin
                       -- PROJECT this is really ugly! Those inductions should work better...
                       tidy,
                       induction j,
                       tidy,
                       exact C.compose k f,
                       induction j,
                       induction k_1,
                       tidy,
                       induction f_1,
                       tidy,
                       induction k_1,
                       tidy,
                       induction f_1
                     end,
    factorisation := ♯,
    uniqueness    := begin
                       tidy,
                       let Z_cone : Cone (ParallelPair_functor f g) := {
                         cone_point := Z,
                         cone_maps := λ j : Two, C.compose a (lim.terminal_object.cone_maps j),
                         commutativity := begin
                                            tidy,
                                            {
                                              have c := lim.terminal_object.commutativity,
                                              erw @c Two._0 Two._1 Two._0,
                                            },
                                            {
                                              have c := lim.terminal_object.commutativity,
                                              erw @c Two._0 Two._1 Two._1,
                                            },
                                          end
                       },
                       have p := lim.uniqueness_of_morphisms_to_terminal_object Z_cone ⟨ a, _ ⟩ ⟨ b, _ ⟩,
                       exact congr_arg ConeMorphism.cone_morphism p,
                       -- finally, take care of those placeholders
                       tidy,
                       have c := lim.terminal_object.commutativity,
                       rw ← @c Two._0 Two._1 Two._1,
                       repeat { rw ← C.associativity },
                       rw witness, 
                     end
  }                       
}

instance Products_from_Limits (C : Category.{u₁ u₂}) [Complete.{u₁ u₂ u₃ u₄} C] : has_Products.{u₁ u₂ u₃} C := {
    product := λ {I : Type u₃} (F : I → C.Obj), 
                 let lim_F := limitCone (Functor.fromFunction F) in
                  {
                    product       := lim_F.terminal_object.cone_point,
                    projection    := λ i, lim_F.terminal_object.cone_maps i,
                    uniqueness    := λ Z f g, begin
                                                intros, 
                                                have p := lim_F.uniqueness_of_morphisms_to_terminal_object, 
                                                have q := p _ (ConeMorphism_from_map_to_limit f)
                                                  { cone_morphism := g, commutativity := begin tidy, simp *, end }, -- (`simp *` isn't good in tidy; it's really slow)
                                                exact congr_arg ConeMorphism.cone_morphism q, -- PROJECT surely this line can be automated: if you know a = b, you know a.x = b.x
                                              end,
                    map           := λ Z i, (lim_F.morphism_to_terminal_object_from { 
                                              cone_point := Z, 
                                              cone_maps := i, 
                                              commutativity := ♯ 
                                            }).cone_morphism
                  }
}

end categories.universal