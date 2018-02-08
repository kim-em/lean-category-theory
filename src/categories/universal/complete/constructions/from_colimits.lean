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
set_option pp.universes true

instance Coequalizers_from_Colimits ( C : Category.{u₁ u₂} ) [ Cocomplete.{u₁ u₂ u₃ u₄} C ] : has_Coequalizers.{u₁ u₂} C :=
{ coequalizer := λ _ _ f g, Equalizer_in_Opposite (@equalizer (Opposite C) _ _ _ f g) }

set_option trace.class_instances true

instance Coproducts_from_Colimits ( C : Category.{u₁ u₂} ) [ Cocomplete.{u₁ u₂ u₃ u₄} C ] : has_Coproducts.{u₁ u₂ u₃} C := {
  coproduct := λ _ F, Product_in_Opposite (@product (Opposite C) _ _ F)
}

end categories.universal
