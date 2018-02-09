-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...isomorphism
import ...natural_transformation
import ...equivalence
import ..comma_categories
import ..universal

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.equivalence
open categories.universal

namespace categories.universal

-- definition comma_Equalizer_to_Equalizer {C : Category} {X Y : C.Obj} {f g : C.Hom X Y} (equalizer : comma.Equalizer f g) : Equalizer f g := sorry

-- definition Equalizer_to_comma_Equalizer {C : Category} {X Y : C.Obj} {f g : C.Hom X Y} (equalizer : Equalizer f g)  : comma.Equalizer f g := sorry

-- definition Equalizers_agree {C : Category} {X Y : C.Obj} (f g : C.Hom X Y) : Isomorphism CategoryOfTypes (comma.Equalizer f g) (Equalizer f g) := sorry

-- PROJECT prove equalizers are unique

end categories.universal