-- -- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import categories.universal.instances
-- import categories.discrete_category
-- import categories.walking

-- open categories
-- open categories.functor
-- open categories.initial

-- namespace categories.universal

-- structure CreatesLimitsOfShape {A B : Category} (F : Functor A B) (I : Category)  :=
--   (cone_from_limit : Π (D : Functor I A) (q : LimitCone (FunctorComposition D F)), Cone D)
--   (image_of_cone_is_limit_cone : Π (D : Functor I A) (q : LimitCone (FunctorComposition D F)), @is_terminal (Cones (FunctorComposition D F)) (F.onCones (cone_from_limit D q)))
--   (every_such_cone_is_limit_cone : Π (D : Functor I A) (p : Cone D) (w : @is_terminal (Cones (FunctorComposition D F)) (F.onCones p)), @is_terminal (Cones D) p)

-- structure CreatesLimits {A B : Category} (F : Functor A B) := 
--   (over : Π (I : Category), CreatesLimitsOfShape F I)

-- structure CreatesProducts {A B : Category} (F : Functor A B) :=
--   (over : Π (I : Type), CreatesLimitsOfShape F (DiscreteCategory I))


-- -- PROJECT define CreatesProducts and CreatesEqualizers, and construct CreatesLimits from these.
-- -- PROJECT show various forgetful functors create limits
-- -- PROJECT use this to construct limits in various algebraic categories.

-- end categories.universal