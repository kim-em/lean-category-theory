-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories.isomorphism

structure Isomorphism ( C: Category ) ( X Y : C.Obj ) :=
  (morphism : C.Hom X Y)
  (inverse : C.Hom Y X)
  (witness_1 : C.compose morphism inverse = C.identity X . tidy')
  (witness_2 : C.compose inverse morphism = C.identity Y . tidy')

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

instance Isomorphism_coercion_to_morphism { C : Category } { X Y : C.Obj } : has_coe (Isomorphism C X Y) (C.Hom X Y) :=
  { coe := Isomorphism.morphism }

definition IsomorphismComposition { C : Category } { X Y Z : C.Obj } ( α : Isomorphism C X Y ) ( β : Isomorphism C Y Z ) : Isomorphism C X Z :=
{
  morphism := C.compose α.morphism β.morphism,
  inverse := C.compose β.inverse α.inverse
}

@[applicable] lemma {u1 v1} Isomorphism_pointwise_equal
  { C : Category.{u1 v1} }
  { X Y : C.Obj }
  ( α β : Isomorphism C X Y )
  ( w : α.morphism = β.morphism ) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    simp at w,    
    have p : g = k,
      begin
        -- PROJECT why can't we automate this?
        tidy,
        rewrite ← C.left_identity k,
        rewrite ← wα2,
        rewrite C.associativity,
        simp *,
      end,
    smt_eblast
  end

definition Isomorphism.reverse { C : Category } { X Y : C.Obj } ( I : Isomorphism C X Y ) : Isomorphism C Y X :=
  {
    morphism  := I.inverse,
    inverse   := I.morphism
  }

structure is_Isomorphism { C : Category } { X Y : C.Obj } ( morphism : C.Hom X Y ) :=
  (inverse : C.Hom Y X)
  (witness_1 : C.compose morphism inverse = C.identity X . tidy')
  (witness_2 : C.compose inverse morphism = C.identity Y . tidy')

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

instance is_Isomorphism_coercion_to_morphism { C : Category } { X Y : C.Obj } ( f : C.Hom X Y ): has_coe (is_Isomorphism f) (C.Hom X Y) :=
  { coe := λ _, f }

definition Epimorphism { C : Category } { X Y : C.Obj } ( f : C.Hom X Y ) := Π { Z : C.Obj } ( g h : C.Hom Y Z ) ( w : C.compose f g = C.compose f h), g = h
definition Monomorphism { C : Category } { X Y : C.Obj } ( f : C.Hom X Y ) := Π { Z : C.Obj } ( g h : C.Hom Z X ) ( w : C.compose g f = C.compose h f), g = h

end categories.isomorphism
