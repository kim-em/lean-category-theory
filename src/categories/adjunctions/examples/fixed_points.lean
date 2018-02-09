-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ...adjunctions
import ...full_subcategory

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.isomorphism
open categories.types
open categories.functor_categories

namespace categories.adjunctions

-- EXERCISE
-- cf Leinster 2.2.11
definition left_fixed_points  {C D : Category} {L : Functor C D} {R : Functor D C} (A : Adjunction L R)
  : Category := FullSubcategory C (λ X, is_Isomorphism (A.unit X))
definition right_fixed_points {C D : Category} {L : Functor C D} {R : Functor D C} (A : Adjunction L R)
  : Category := FullSubcategory D (λ X, is_Isomorphism (A.counit X))

-- Now we need to express the idea that functors restrict to a full subcategory with image in another full subcategory,
-- and that these restrictions give an equivalence.

end categories.adjunctions