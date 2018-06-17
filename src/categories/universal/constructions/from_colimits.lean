-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.constructions.from_limits
import categories.universal.opposites

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.initial
open categories.walking
open categories.opposites
open categories.universal.opposites

namespace categories.universal

universes u₁
variable {C : Type (u₁+1)}
variable [large_category C]

instance Coequalizers_from_Colimits [Cocomplete C] : has_Coequalizers.{u₁+1 u₁} C :=
{coequalizer := λ _ _ f g, Coequalizer_from_Equalizer_in_Opposite (@equalizer.{u₁+1 u₁} (Cᵒᵖ) _ _ _ _ f g)}

instance Coproducts_from_Colimits [Cocomplete C] : has_Coproducts C := {
  coproduct := λ _ F, Coproduct_from_Product_in_Opposite (@product (Cᵒᵖ) _ (@universal.Products_from_Limits (Cᵒᵖ) _ (universal.opposites.Opposite_Complete_of_Cocomplete)) _ F)
}

end categories.universal
