-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .limits_from

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

instance Colimits_from_Coproducts_and_Coequalizers ( C : Category.{u₁ u₂} ) [ has_Coproducts.{u₁ u₂ u₃} C ] [ has_Coequalizers.{u₁ u₂} C ] : Cocomplete.{u₁ u₂ u₃ u₃} C := 
Cocomplete_of_Opposite_Complete (@universal.Limits_from_Products_and_Equalizers (Opposite C))

end categories.universal
