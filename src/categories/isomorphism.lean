-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories.isomorphism
universes u v

variable {O : Type u}
variables {X Y Z : O}

structure Isomorphism [C : category.{u v} O] (X Y : O) :=
  (morphism : Hom X Y)
  (inverse : Hom Y X)
  (witness_1 : morphism >> inverse = 𝟙 X . tidy')
  (witness_2 : inverse >> morphism = 𝟙 Y . tidy')

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [simp,ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

instance Isomorphism_coercion_to_morphism [C : category.{u v} O] : has_coe (Isomorphism X Y) (Hom X Y) :=
  {coe := Isomorphism.morphism}

definition IsomorphismComposition [C : category.{u v} O] (α : Isomorphism X Y) (β : Isomorphism Y Z) : Isomorphism X Z :=
{
  morphism := α.morphism >> β.morphism,
  inverse := β.inverse >> α.inverse
}

@[applicable] lemma Isomorphism_pointwise_equal
  [C : category.{u v} O]
  (α β : Isomorphism.{u v} X Y)
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
        rewrite category.associativity,
        simp *,
      end,
    smt_eblast
  end

definition Isomorphism.reverse [C : category O] (I : Isomorphism X Y) : Isomorphism Y X :=
  {
    morphism  := I.inverse,
    inverse   := I.morphism
 }

structure is_Isomorphism [C : category O] (morphism : Hom X Y) :=
  (inverse : Hom Y X)
  (witness_1 : morphism >> inverse = 𝟙 X . tidy')
  (witness_2 : inverse >> morphism = 𝟙 Y . tidy')

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [simp,ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

instance is_Isomorphism_coercion_to_morphism [C : category O] (f : Hom X Y): has_coe (is_Isomorphism f) (Hom X Y) :=
  {coe := λ _, f}

definition Epimorphism [C : category O] (f : Hom X Y) := Π (g h : Hom Y Z) (w : f >> g = f >> h), g = h
definition Monomorphism [C : category O] (f : Hom X Y) := Π (g h : Hom Z X) (w : g >> f = h >> f), g = h

end categories.isomorphism
