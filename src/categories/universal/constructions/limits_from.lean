-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.complete
import categories.walking
import tidy.transport

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.initial
open categories.walking
open categories.util.finite

namespace categories.universal

universes u₁
variable {C : Type (u₁+1)}
variable [category C]
universes u₂
variable {D : Type (u₂+1)}
variable [category D]

def id_eq {X Y : C} (p : X = Y) : X ⟶ Y := by convert (𝟙 X); tidy
@[simp,ematch] lemma Functor.on_id_eq (F : C ↝ D) {X Y : C} (p : X = Y) : F &> (id_eq p) = id_eq (congr_arg F.onObjects p) :=
begin
  unfold id_eq,
  tidy,
end
@[simp,ematch] lemma id_eq_id_eq {X Y Z : C} (p : X = Y) (q : Y = Z) : (id_eq p) ≫ (id_eq q) = id_eq (eq.trans p q) := 
begin
  unfold id_eq,
  tidy,
end
@[simp,ematch] lemma id_eq_id (X : C) (p : X = X) : id_eq p = 𝟙 X := by refl


instance Limits_from_Products_and_Equalizers [has_Products C] [has_Equalizers C] : Complete C := {
  limitCone := λ J _ F,
    begin
    resetI,
    exact 
    let product_over_objects   := product (λ p, F +> (small.up p)) in
    let product_over_morphisms := product (λ f : (Σ p : J × J, (small.up p.1) ⟶ (small.up p.2)), F +> (small.up f.1.2)) in 
    let source    := product_over_morphisms.map (λ f, (product_over_objects.projection f.1.1) ≫ (F &> f.2))  in
    let target    := product_over_morphisms.map (λ f, product_over_objects.projection f.1.2) in
    let equalizer := equalizer source target in {
      terminal_object     := {
        cone_point    := equalizer.equalizer,
        cone_maps     := λ j : (small J), equalizer.inclusion ≫ (product_over_objects.projection j.down) ≫ id_eq (by obviously),
        commutativity := λ j k f, begin
                                   have p := congr_arg (λ i, i ≫ (product_over_morphisms.projection ⟨ (j.down, k.down), (id_eq (by obviously)) ≫ f ≫ (id_eq (by obviously))⟩)) equalizer.witness,                                
                                   tidy,
                                   conv { to_rhs, rw ← category.associativity },
                                   rw ← p,
                                   tidy, -- PROJECT automation
                                  end
     },
     morphism_to_terminal_object_from := λ cone : Cone F, {
        cone_morphism := /- we need a morphism from the tip of f to the equalizer -/
                         equalizer.map
                           (product_over_objects.map (λ j, cone.cone_maps (small.up j))) (by obviously),
        commutativity := begin 
                           tidy, 
                           rw ← category.associativity, 
                           rw equalizer.factorisation, 
                           rw ← category.associativity, 
                           rw product_over_objects.factorisation,
                           rw ← Functor.on_id_eq,
                           rw cone.commutativity,
                           simp, -- PROJECT automate
                         end
     },
     uniqueness_of_morphisms_to_terminal_object :=
     begin
       tidy,
       have pf := f.commutativity (small.up i),
       have pg := g.commutativity (small.up i),
       tidy,
     end,
   }
   end
}

end categories.universal