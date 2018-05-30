-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.types

open categories
open categories.functor
open categories.types

universes u v

instance functor_of_Functor (F : Functor (Type u) (Type v)) : functor F.onObjects := 
{ map := λ _ _ f, F &> f }

local attribute [tidy] dsimp'

-- TODO yuck, automate
instance lawful_functor_of_Functor (F : Functor (Type u) (Type v)) : is_lawful_functor (F.onObjects) := 
{ id_map := by obviously,
  comp_map := begin
                intros, 
                dsimp', 
                calc (F &> λ (x : α), h (g x)) x = (F &> (g ≫ h)) x      : by obviously
                                             ... = (F &> h) ((F &> g) x) : by obviously
              end
}

attribute [ematch] is_lawful_functor.comp_map

definition Functor_of_functor (g : Type u → Type v) [functor g] [is_lawful_functor g] : Functor (Type u) (Type v) := 
{ onObjects := g,
  onMorphisms := λ X Y f z, f <$> z }