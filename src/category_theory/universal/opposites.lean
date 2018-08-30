-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Daniel Barter

import category_theory.opposites
import category_theory.equivalence
import category_theory.universal.cones
import category_theory.universal.colimits


open category_theory
open category_theory.universal

namespace category_theory.universal

universes u v

section
variable {C : Type u}
variable [𝒞 : category.{u v} C]
include 𝒞

def opposite_fan_of_cofan {β : Type v} (f : β → C) (t : cofan f) : @fan (Cᵒᵖ) _ _ f :=
{ X := t.X,
  π := λ b, t.ι b } 
def fan_of_opposite_cofan {β : Type v} (f : β → C) (t : @cofan (Cᵒᵖ) _ _ f) : fan f :=
{ X := t.X,
  π := λ b, t.ι b } 

instance [has_coproducts.{u v} C] : has_products.{u v} (Cᵒᵖ) := 
{ prod := λ {β : Type v} (f : β → C), fan_of_opposite_cofan f sorry,
  is_product := sorry }
instance [has_coequalizers.{u v} C] : has_equalizers.{u v} (Cᵒᵖ) := sorry

-- making this an instance would cause loops:
def has_colimits_of_opposite_has_limits [has_limits.{u v} (Cᵒᵖ)] : has_colimits.{u v} C := sorry

end

end category_theory.universal
