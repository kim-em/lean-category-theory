-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..types
import ..full_subcategory
import ..util.finite

namespace categories.types

open categories
open categories.util.finite

universe u

definition DecidableType := Σ X : Type u, decidable_eq X
definition FiniteType := Σ X : Type u, Finite X

instance CategoryOfDecidableTypes : category DecidableType := categories.FullSubcategory decidable_eq -- TODO by apply_instance?
instance CategoryOfFiniteTypes : category FiniteType := categories.FullSubcategory Finite

-- PROJECT we could construct an embedding of Finite into Decidable?

end categories.types
