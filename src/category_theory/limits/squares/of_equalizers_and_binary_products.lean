-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.equalizers
import category_theory.limits.binary_products
import category_theory.limits.squares

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section
variables [has_binary_products.{u v} C] [has_equalizers.{u v} C]

instance : has_pullbacks.{u v} C :=
{ pullback := λ Y₁ Y₂ Z r₁ r₂,
    let f := prod.π₁ Y₁ Y₂ ≫ r₁ in
    let g := prod.π₂ Y₁ Y₂ ≫ r₂ in
    { X := equalizer f g, π₁ := equalizer.ι f g ≫ prod.π₁ Y₁ Y₂, π₂ := equalizer.ι f g ≫ prod.π₂ Y₁ Y₂ },
  is_pullback := λ Y₁ Y₂ Z r₁ r₂,
  { lift := λ s, equalizer.lift (prod.lift s.π₁ s.π₂)
                 begin -- FIXME why not obviously?
                   rw [← category.assoc, ← category.assoc],
                   simp,
                   exact s.w
                 end } }.
end

-- FIXME why does this time out??
section
variables [has_binary_coproducts.{u v} C] [has_coequalizers.{u v} C]

instance : has_pushouts.{u v} C :=
{ pushout := λ Y₁ Y₂ Z r₁ r₂,
    let f := r₁ ≫ coprod.ι₁ Y₁ Y₂ in
    let g := r₂ ≫ coprod.ι₂ Y₁ Y₂ in
    { X := coequalizer f g, ι₁ := coprod.ι₁ Y₁ Y₂ ≫ coequalizer.π f g, ι₂ := coprod.ι₂ Y₁ Y₂ ≫ coequalizer.π f g },
  is_pushout := λ Y₁ Y₂ Z r₁ r₂,
  { lift := λ s, coequalizer.desc (coprod.desc s.ι₁ s.ι₂)
                 begin -- FIXME why not obviously?
                   rw [← category.assoc, ← category.assoc],
                   simp,
                   exact s.w
                 end } }.
end

end category_theory.limits