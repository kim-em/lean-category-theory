-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories.isomorphism

structure Isomorphism ( C: Category ) ( X Y : C.Obj ) :=
  (morphism : C.Hom X Y)
  (inverse : C.Hom Y X)
  (witness_1 : C.compose morphism inverse = C.identity X)
  (witness_2 : C.compose inverse morphism = C.identity Y)

attribute [simp,ematch] Isomorphism.witness_1 Isomorphism.witness_2

instance Isomorphism_coercion_to_morphism { C : Category } { X Y : C.Obj } : has_coe (Isomorphism C X Y) (C.Hom X Y) :=
  { coe := Isomorphism.morphism }

definition IsomorphismComposition { C : Category } { X Y Z : C.Obj } ( α : Isomorphism C X Y ) ( β : Isomorphism C Y Z ) : Isomorphism C X Z :=
{
  morphism := C.compose α.morphism β.morphism,
  inverse := C.compose β.inverse α.inverse,
  witness_1 := ♮,
  witness_2 := ♮
}

@[applicable] lemma {u1 v1} Isomorphism_applicable_equal
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
        rewrite - C.left_identity k,
        rewrite - wα2,
        rewrite C.associativity,
        rewrite w,
        rewrite wβ1,
        simp
      end,
    smt_eblast
  end

definition Isomorphism.reverse { C : Category } { X Y : C.Obj } ( I : Isomorphism C X Y ) : Isomorphism C Y X :=
  {
    morphism  := I.inverse,
    inverse   := I.morphism,
    witness_1 := I.witness_2,
    witness_2 := I.witness_1
  }

structure is_Isomorphism { C : Category } { X Y : C.Obj } ( morphism : C.Hom X Y ) :=
  (inverse : C.Hom Y X)
  (witness_1 : C.compose morphism inverse = C.identity X)
  (witness_2 : C.compose inverse morphism = C.identity Y)

attribute [simp,ematch] is_Isomorphism.witness_1 is_Isomorphism.witness_2

instance is_Isomorphism_coercion_to_morphism { C : Category } { X Y : C.Obj } ( f : C.Hom X Y ): has_coe (is_Isomorphism f) (C.Hom X Y) :=
  { coe := λ _, f }

definition Epimorphism { C : Category } { X Y : C.Obj } ( f : C.Hom X Y ) := Π { Z : C.Obj } ( g h : C.Hom Y Z ) ( w : C.compose f g = C.compose f h), g = h
definition Monomorphism { C : Category } { X Y : C.Obj } ( f : C.Hom X Y ) := Π { Z : C.Obj } ( g h : C.Hom Z X ) ( w : C.compose g f = C.compose h f), g = h

end categories.isomorphism
