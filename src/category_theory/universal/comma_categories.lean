-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..walking
import .initial

open categories
open categories.isomorphism
open categories.graph
open categories.functor
open categories.natural_transformation
open categories.initial
open categories.walking

namespace categories.comma

-- The diagonal functor sends X to the constant functor that sends everything to X.
definition DiagonalFunctor ( J C : Category ) : Functor C (FunctorCategory J C) :=
{
  onObjects     := λ X : C.Obj, {
    onObjects     := λ _, X,
    onMorphisms   := λ _ _ _, C.identity X,
    identities    := ♮,
    functoriality := ♮
  },
  onMorphisms   := λ X Y f, {
    components := λ _, f,
    naturality := ♮
  },
  identities    := ♮,
  functoriality := ♮
}

-- unfortunately one can't coerce along subtype.val
open subtype

local attribute [ematch] subtype.property

-- The elaborator has some trouble understanding what p.2.2 and q.2.2 mean below.
-- Leo suggested the following work-around, at <https://groups.google.com/d/msg/lean-user/8jW4BIUFl24/MOtgbpfqCAAJ>.
local attribute [elab_simple]  sigma.snd

definition CommaCategory
  { A B C : Category }
  ( S : Functor A C ) ( T : Functor B C ) : Category :=
{
  Obj      := Σ a : A.Obj, Σ b : B.Obj, C.Hom (S.onObjects a) (T.onObjects b),
  Hom      := λ p q, { gh : (A.Hom p.1 q.1) × (B.Hom p.2.1 q.2.1) // C.compose (S.onMorphisms gh.1) q.2.2 = C.compose p.2.2 (T.onMorphisms gh.2) },
  identity := λ p, ⟨ (A.identity p.1, B.identity p.2.1), ♮ ⟩,
  compose  := λ p q r f g, ⟨ (A.compose (val f).1 (val g).1, B.compose (val f).2 (val g).2), ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♮
}

definition ObjectAsFunctor { C : Category } ( X : C.Obj ) : Functor (DiscreteCategory unit) C :=
{
  onObjects     := λ _, X,
  onMorphisms   := λ _ _ _, C.identity X,
  identities    := ♮,
  functoriality := ♮
}

definition SliceCategory   { C : Category } ( X : C.Obj ) := CommaCategory (IdentityFunctor C) (ObjectAsFunctor X)
definition CosliceCategory { C : Category } ( X : C.Obj ) := CommaCategory (ObjectAsFunctor X) (IdentityFunctor C)

-- In Cones, we have
--   A = C
--   B = .
--   C = FunctorCategory J C
definition Cones   { J C : Category } ( F : Functor J C ) := CommaCategory (DiagonalFunctor J C)                      (ObjectAsFunctor F)
definition Cocones { J C : Category } ( F : Functor J C ) := CommaCategory (@ObjectAsFunctor (FunctorCategory J C) F) (DiagonalFunctor J C)

definition Limit   { J C : Category } ( F: Functor J C ) := TerminalObject (Cones   F)
definition Colimit { J C : Category } ( F: Functor J C ) := InitialObject  (Cocones F)

definition BinaryProduct   { C : Category } ( α β : C.Obj )                     := Limit   (Pair_functor α β)
definition BinaryCoproduct { C : Category } ( α β : C.Obj )                     := Colimit (Pair_functor α β)
definition {u} Product     { C : Category } { I : Type u } ( X : I → C.Obj )   := Limit   (Functor.fromFunction X)
definition {u} Coproduct   { C : Category } { I : Type u } ( X : I → C.Obj )   := Colimit (Functor.fromFunction X)
definition Equalizer       { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) := Limit   (ParallelPair_functor f g)
definition Coequalizer     { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) := Colimit (ParallelPair_functor f g)

end categories.comma

