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

set_option pp.universes true
@[reducible] definition DecidableType := @psigma (Type u) decidable_eq 
definition FiniteType := Σ X : Type u, Finite X

definition CategoryOfDecidableTypes : category DecidableType := by apply_instance

-- PROJECT
-- definition CategoryOfFiniteTypes : category FiniteType := @categories.FullSubcategory (Type u) _ (λ X, Finite X)

-- PROJECT we could construct an embedding of Finite into Decidable?

end categories.types
