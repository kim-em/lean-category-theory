-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import categories.types
import categories.full_subcategory

namespace categories.types

open categories

universe u

definition DecidableType := Σ X : Type u, decidable_eq X

instance CategoryOfDecidableTypes : large_category DecidableType := large_category_of_uv_category (by unfold DecidableType; apply_instance)

end categories.types
