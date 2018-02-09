-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .from_limits

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.initial
open categories.walking
open categories.util.finite
open categories.opposites
open categories.universal.opposites

namespace categories.universal

universes u₁ u₂ u₃ u₄

instance Coequalizers_from_Colimits (C : Category.{u₁ u₂}) [Cocomplete.{u₁ u₂ u₃ u₄} C] : has_Coequalizers.{u₁ u₂} C :=
{coequalizer := λ _ _ f g, Coequalizer_from_Equalizer_in_Opposite (@equalizer (Opposite C) _ _ _ f g)}

instance Coproducts_from_Colimits (C : Category.{u₁ u₂}) [Cocomplete.{u₁ u₂ u₃ u₃} C] : has_Coproducts.{u₁ u₂ u₃} C := {
  coproduct := λ _ F, Coproduct_from_Product_in_Opposite (@product.{u₁ u₂ u₃} (Opposite C) (@universal.Products_from_Limits (Opposite C) (universal.opposites.Opposite_Complete_of_Cocomplete)) _ F)
}

end categories.universal
