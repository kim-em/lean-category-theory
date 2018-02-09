-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories.isomorphism
universes u v

structure Isomorphism {O : Type u} [C: category.{u v} O] (X Y : O) :=
  (morphism : Hom X Y)
  (inverse : Hom Y X)
  (witness_1 : morphism >> inverse = 𝟙 X . tidy')
  (witness_2 : inverse >> morphism = 𝟙 Y . tidy')

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [simp,ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

instance Isomorphism_coercion_to_morphism {O} [C : category O] {X Y : O} : has_coe (Isomorphism X Y) (Hom X Y) :=
  {coe := Isomorphism.morphism}

definition IsomorphismComposition {O} [C : category O] {X Y Z : O} (α : Isomorphism X Y) (β : Isomorphism Y Z) : Isomorphism X Z :=
{
  morphism := α.morphism >> β.morphism,
  inverse := β.inverse >> α.inverse
}
set_option pp.universes true
@[applicable] lemma {u1 v1} Isomorphism_pointwise_equal
  {O : Type u1}
  [C : category.{u1 v1} O]
  {X Y : O}
  (α β : Isomorphism.{u1 v1} X Y)
  (w : α.morphism = β.morphism) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    simp at w,    
    have p : g = k,
      begin
        -- PROJECT why can't we automate this?
        tidy,
        resetI,
        rewrite ← category.left_identity k,
        rewrite ← wα2,
        rewrite C.associativity,
        simp *,
      end,
    smt_eblast
  end

definition Isomorphism.reverse {C : Category} {X Y : C.Obj} (I : Isomorphism C X Y) : Isomorphism C Y X :=
  {
    morphism  := I.inverse,
    inverse   := I.morphism
 }

structure is_Isomorphism {C : Category} {X Y : C.Obj} (morphism : C.Hom X Y) :=
  (inverse : C.Hom Y X)
  (witness_1 : C.compose morphism inverse = C.identity X . tidy')
  (witness_2 : C.compose inverse morphism = C.identity Y . tidy')

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [simp,ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

instance is_Isomorphism_coercion_to_morphism {C : Category} {X Y : C.Obj} (f : C.Hom X Y): has_coe (is_Isomorphism f) (C.Hom X Y) :=
  {coe := λ _, f}

definition Epimorphism {C : Category} {X Y : C.Obj} (f : C.Hom X Y) := Π {Z : C.Obj} (g h : C.Hom Y Z) (w : C.compose f g = C.compose f h), g = h
definition Monomorphism {C : Category} {X Y : C.Obj} (f : C.Hom X Y) := Π {Z : C.Obj} (g h : C.Hom Z X) (w : C.compose g f = C.compose h f), g = h

end categories.isomorphism
