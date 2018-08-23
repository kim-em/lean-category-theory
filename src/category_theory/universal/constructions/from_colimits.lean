-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.constructions.from_limits
import category_theory.universal.opposites

open category_theory
open category_theory.initial
open category_theory.walking
open category_theory.universal.opposites

namespace category_theory.universal

universes u₁
variable {C : Type (u₁+1)}
variable [large_category C]

instance Coequalizers_from_Colimits [Cocomplete C] : has_Coequalizers.{u₁+1 u₁} C :=
{coequalizer := λ _ _ f g, Coequalizer_from_Equalizer_in_Opposite (@equalizer.{u₁+1 u₁} (Cᵒᵖ) _ _ _ _ f g)}

instance Coproducts_from_Colimits [Cocomplete C] : has_Coproducts C := {
  coproduct := λ _ F, Coproduct_from_Product_in_Opposite (@product (Cᵒᵖ) _ (@universal.Products_from_Limits (Cᵒᵖ) _ (universal.opposites.Opposite_Complete_of_Cocomplete)) _ F)
}

end category_theory.universal
