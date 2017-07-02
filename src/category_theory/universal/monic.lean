-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .universal
import ..monic

open categories
open categories.universal
open categories.isomorphism

namespace categories

structure RegularMonic { C : Category } { X Y : C.Obj } ( f : C.Hom X Y ) :=
  ( Z : C.Obj )
  ( a b : C.Hom Y Z )
  ( e : Equalizer a b )
  ( i : Isomorphism C e.equalizer X )
  ( w : e.inclusion = C.compose i.morphism f )

-- PROJECT
-- lemma SplitMonic_implies_RegularMonic
--   { C : Category } 
--   { X Y : C.Obj } 
--   { f : C.Hom X Y } 
--   ( s : SplitMonic f ) : RegularMonic f := sorry

-- PROJECT
-- lemma RegularMonic_implies_Monic
--   { C : Category } 
--   { X Y : C.Obj } 
--   { f : C.Hom X Y } 
--   ( s : RegularMonic f ) : Monic f := sorry

structure RegularEpic { C : Category } { Y Z : C.Obj } ( f : C.Hom Y Z ) :=
  ( X : C.Obj )
  ( a b : C.Hom X Y )
  ( c : Coequalizer a b )
  ( i : Isomorphism C c.coequalizer Z )
  ( w : c.projection = C.compose f i.inverse )

end categories