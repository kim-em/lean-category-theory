-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..types

open categories
open categories.functor
open categories.types

universes u v

@[simp] private lemma functor_identities (F : Functor (Type u) (Type v)) (α : Type u) (x : F α) : (F &> id) x = x := 
begin
    have p := Functor_to_Types.identities F x,
    tidy,
end

instance functor_of_Functor (F : Functor (Type u) (Type v)) : functor F := {
    map := λ _ _ f, F &> f,
    id_map := ♯,
    map_comp := begin 
                 tidy, 
                 have p := Functor_to_Types.functoriality F g h x,
                 rw ← p,
                 tidy,
                end
}

local attribute [simp] functor.id_map

definition Functor_of_functor (g : Type u → Type v) [functor g] : Functor (Type u) (Type v) := {
    onObjects := g,
    onMorphisms := λ X Y f z, (has_map.map f) z,
    functoriality := begin tidy, rw ← functor.map_comp, end
}