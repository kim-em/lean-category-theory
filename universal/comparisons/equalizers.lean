-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...isomorphism
import ...natural_transformation
import ...examples.types.types
import ...equivalence
import ..comma_categories
import ..universal

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.equivalence
open tqft.categories.examples.types
open tqft.categories.universal

namespace tqft.categories.universal

-- definition comma_Equalizer_to_Equalizer { C : Category } { X Y : C.Obj } { f g : C.Hom X Y } ( equalizer : comma.Equalizer f g ) : Equalizer f g := sorry

-- definition Equalizer_to_comma_Equalizer { C : Category } { X Y : C.Obj } { f g : C.Hom X Y } ( equalizer : Equalizer f g )  : comma.Equalizer f g := sorry

-- definition Equalizers_agree { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) : Isomorphism CategoryOfTypes (comma.Equalizer f g) (Equalizer f g) := sorry

-- PROJECT prove equalizers are unique

end tqft.categories.universal