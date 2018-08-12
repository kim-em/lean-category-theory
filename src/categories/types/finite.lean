-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.types
import categories.full_subcategory

namespace category_theory.types

open category_theory

universe u

def decidable_type := Σ X : Type u, decidable_eq X

instance : large_category decidable_type := by unfold decidable_type; apply_instance

end category_theory.types
