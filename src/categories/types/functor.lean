-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..types

open categories
open categories.functor
open categories.types

universes u v

instance functor_of_Functor (F : Functor (Type u) (Type v)) : functor (F.onObjects) := {
    map := λ _ _ f, (F.onMorphisms (ulift.up f)).down,
    id_map := ♯,
    map_comp := begin 
                 tidy, 
                 have p := Functor_to_Types_functoriality F (ulift.up g) (ulift.up h) x,
                 rw p,
                end
}

local attribute [simp] functor.id_map

definition Functor_of_functor (g : Type u → Type v) [functor g] : Functor (Type u) (Type v) := {
    onObjects := g,
    onMorphisms := λ X Y f, ulift.up (λ z : g X, (has_map.map f.down) z),
    functoriality := begin tidy, rw ← functor.map_comp, end
}