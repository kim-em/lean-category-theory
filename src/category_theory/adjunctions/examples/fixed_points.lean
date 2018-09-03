-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.adjunctions
import category_theory.full_subcategory

open category_theory

namespace category_theory.adjunctions

universe u

variable {C : Type (u+1)}
variable [large_category C]
variable {D : Type (u+1)}
variable [large_category D]

-- EXERCISE
-- cf Leinster 2.2.11
def left_fixed_points  {L : C ⥤ D} {R : D ⥤ C} (A : Adjunction L R) : large_category (Σ X : C, is_iso (A.unit X)) := by apply_instance
def right_fixed_points {L : C ⥤ D} {R : D ⥤ C} (A : Adjunction L R) : large_category (Σ X : D, is_iso (A.counit X)) := by apply_instance

-- Now we need to express the idea that functors restrict to a full subcategory with image in another full subcategory,
-- and that these restrictions give an equivalence.

end category_theory.adjunctions