-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..complete
import ..opposites
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

universes u₁
variable {C : Type (u₁+2)}
variable [category C]

instance Limits_from_Products_and_Equalizers [has_Products C] [has_Equalizers C] : Complete C := {
  limitCone := λ J _ F,
    begin
    resetI,
    exact 
    let product_over_objects   := product.{u₁+1} (F.onObjects) in
    let product_over_morphisms := product (λ f : (Σ s : J, Σ t : J, Hom s t), F.onObjects f.2.1) in -- TODO this would be cleaner as a sigma over J × J
    let source    := product_over_morphisms.map (λ f, (product_over_objects.projection f.1) ≫ (F.onMorphisms f.2.2))  in
    let target    := product_over_morphisms.map (λ f, product_over_objects.projection f.2.1) in
    let equalizer := equalizer source target in {
      terminal_object     := {
        cone_point    := equalizer.equalizer,
        cone_maps     := λ j : J, equalizer.inclusion ≫ (product_over_objects.projection j),
        commutativity := λ j k f, begin
                                   have p := congr_arg (λ i, i ≫ (product_over_morphisms.projection ⟨ j, ⟨ k, f ⟩ ⟩)) equalizer.witness,                                
                                   tidy,
                                  end
     },
      morphism_to_terminal_object_from := λ cone : Cone F, {
        cone_morphism := /- we need a morphism from the tip of f to the equalizer -/
                         equalizer.map
                           (product_over_objects.map cone.cone_maps) ♯
     }
   }
   end
}

end categories.universal