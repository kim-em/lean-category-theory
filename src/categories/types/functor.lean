-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.types

open categories
open categories.functor
open categories.types

universes u v

@[simp] private lemma functor_identities (F : Functor (Type u) (Type v)) (α : Type u) (x : F +> α) : (F &> id) x = x := by obviously

instance functor_of_Functor (F : Functor (Type u) (Type v)) : functor F.onObjects := 
{ map := λ _ _ f, F &> f }

local attribute [tidy] dsimp'

instance lawful_functor_of_Functor (F : Functor (Type u) (Type v)) : is_lawful_functor (F.onObjects) := 
begin
fsplit,
apply_auto_param,
intros,
dsimp',
simp,
intros,
dsimp,
dsimp {unfold_reducible:=tt},
dsimp',
simp,
-- tidy {max_steps:=1,trace_result:=tt},
sorry,
end

attribute [ematch] is_lawful_functor.comp_map

definition Functor_of_functor (g : Type u → Type v) [functor g] [is_lawful_functor g] : Functor (Type u) (Type v) := 
{ onObjects := g,
  onMorphisms := λ X Y f z, f <$> z }