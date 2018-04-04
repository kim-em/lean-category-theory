-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..types
import ..full_subcategory

namespace categories.types

open categories

universe u

definition DecidableType := Σ X : Type u, decidable_eq X

instance CategoryOfDecidableTypes : category DecidableType := categories.SigmaCategory decidable_eq -- TODO by apply_instance?

end categories.types
