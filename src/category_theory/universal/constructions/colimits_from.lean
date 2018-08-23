-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.universal.constructions.limits_from
import category_theory.universal.opposites

open category_theory
open category_theory.initial
open category_theory.walking
open category_theory.universal.opposites

namespace category_theory.universal

universes u₁
variable {C : Type (u₁+1)}
variable [large_category C]

instance Colimits_from_Coproducts_and_Coequalizers [has_Coproducts C] [has_Coequalizers.{u₁+1 u₁} C] : Cocomplete C := 
@Cocomplete_of_Opposite_Complete C _ (@universal.Limits_from_Products_and_Equalizers (Cᵒᵖ) _ (universal.opposites.Opposite_has_Products_of_has_Coproducts) (universal.opposites.Opposite_has_Equalizers_of_has_Coequalizers))

end category_theory.universal
