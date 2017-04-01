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
definition Cones_agree { J C : Category } ( F: Functor J C ) : Isomorphism CategoryOfTypes (comma.Cones F)^.Obj (Cone F) := sorry
definition ConeCategories_agree { J C : Category } ( F: Functor J C ) : Isomorphism CategoryOfCategoriesAndFunctors (comma.Cones F) (Cones F) := sorry

lemma Equalizers_agree { C : Category } { α β : C^.Obj } ( f g : C^.Hom α β )
 : @Isomorphism CategoryOfTypes (comma.Equalizer f g) (Equalizer f g) :=
 {
  morphism := sorry,  
  inverse  := sorry,
  witness_1 := sorry,
  witness_2 := sorry
}

-- lemma Equalizers_are_unique
--   { C : Category }  
--   { X Y : C^.Obj } 
--   ( f g : C^.Hom X Y )
--    : unique_up_to_isomorphism (Equalizer f g) Equalizer.equalizer
--    := λ (E1 E2 : Equalizer f g), 
--        comma.InitialObjects_are_unique (Isomorphism.inverse (Equalizers_agree f g) E1) ((Equalizers_agree f g)^.inverse E2)
