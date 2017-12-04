-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..adjunctions
import ..universal.comma_categories

open categories
open categories.functor
open categories.natural_transformation
open categories.comma
open categories.initial

namespace categories.adjunctions

-- PROJECT
-- definition unit_component_in_slice_category
--   { C D : Category } { L : Functor C D } { R : Functor D C } ( A : Adjunction L R ) ( X : C.Obj )
--     : (SliceCategory X).Obj := sorry

-- definition unit_components_initial_in_slice_category
--   { C D : Category } { L : Functor C D } { R : Functor D C } ( A : Adjunction L R ) ( X : C.Obj ) 
--     : is_initial (unit_component_in_slice_category A X) := sorry

-- and so on

end categories.adjunctions