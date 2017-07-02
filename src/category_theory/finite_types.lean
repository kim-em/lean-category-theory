-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .types
import .full_subcategory
import .util.finite

namespace categories.types

open categories
open categories.util.finite

definition {u} CategoryOfDecidableTypes : Category := Full_Subcategory CategoryOfTypes decidable_eq
definition {u} CategoryOfFiniteTypes : Category := Full_Subcategory CategoryOfTypes Finite

-- PROJECT we could construct an embedding of Finite into Decidable?

end categories.types
