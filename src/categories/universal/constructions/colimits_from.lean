-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.constructions.limits_from
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

instance Colimits_from_Coproducts_and_Coequalizers [has_Coproducts C] [has_Coequalizers.{u₁+1 u₁} C] : Cocomplete C := 
@Cocomplete_of_Opposite_Complete C _ (@universal.Limits_from_Products_and_Equalizers (Cᵒᵖ) _ (universal.opposites.Opposite_has_Products_of_has_Coproducts) (universal.opposites.Opposite_has_Equalizers_of_has_Coequalizers))

end categories.universal
