-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..natural_transformation
import ..examples.types.types
import ..graph
import .comma_categories
import .universal

open tqft.categories
open tqft.categories.functor
open tqft.categories.isomorphism
open tqft.categories.examples.types
open tqft.categories.universal

-- PROJECT give the direct definition of slice and coslice categories, and then prove equivalence with this.

-- PROJECT Give more straightforward definitions, and then show they agree.
-- definition Cone_agrees_with_ExplicitCone { J C : Category } ( F: Functor J C ) : Isomorphism CategoryOfTypes (Cones F)^.Obj (ExplicitCone F) := sorry
-- definition Cones_agrees_with_ExplicitCones { J C : Category } ( F: Functor J C ) : Isomorphism CategoryOfTypes (Cones F) (ExplicitCones F) := sorry

lemma Equalizers_agree { C : Category } { α β : C^.Obj } ( f g : C^.Hom α β )
 : @Isomorphism CategoryOfTypes (comma.Equalizer f g) (Equalizer f g) :=
 {
  morphism := sorry,  
  inverse  := sorry,
  witness_1 := sorry,
  witness_2 := sorry
}
