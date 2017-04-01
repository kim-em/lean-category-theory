-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..natural_transformation
import ..graph

open tqft.categories
open tqft.categories.functor
open tqft.categories.isomorphism

namespace tqft.categories.universal

structure Cone { J C : Category } ( F: Functor J C ) :=
  ( limit : C^.Obj )
  ( maps  : Π X : J^.Obj, C^.Hom limit (F X) )
  ( commutativity : Π X Y : J^.Obj, Π f : J^.Hom X Y, C^.compose (maps X) (F^.onMorphisms f) = maps Y )

structure Equalizer { C : Category } { α β : C^.Obj } ( f g : C^.Hom α β ) :=
  ( equalizer : C^.Obj )
  ( inclusion : C^.Hom equalizer α )
  ( witness   : C^.compose inclusion f = C^.compose inclusion g )
  ( factorisation : ∀ { Z : C^.Obj } ( k : C^.Hom Z α ) ( w : C^.compose k f = C^.compose k g ), { i : C^.Hom Z equalizer // C^.compose i inclusion = k } )

end tqft.categories.universal

