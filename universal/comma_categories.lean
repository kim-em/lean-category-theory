-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..discrete_category
import ..graph
import .initial

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.graph
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.initial

namespace tqft.categories.comma

-- The diagonal functor sends X to the constant functor that sends everything to X.
@[unfoldable] definition DiagonalFunctor ( J C : Category ) : Functor C (FunctorCategory J C) :=
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

@[unfoldable] definition CommaCategory
  { A B C : Category }
  ( S : Functor A C ) ( T : Functor B C ) : Category :=
{
  Obj      := Σ a : A.Obj, Σ b : B.Obj, C.Hom (S a) (T b),
  Hom      := λ p q, { gh : (A.Hom p.1 q.1) × (B.Hom p.2.1 q.2.1) // C.compose (S.onMorphisms gh.1) q.2.2 = C.compose p.2.2 (T.onMorphisms gh.2) },
  identity := λ p, ⟨ (A.identity p.1, B.identity p.2.1), ♮ ⟩,
  compose  := λ p q r f g, ⟨ (A.compose (val f).1 (val g).1, B.compose (val f).2 (val g).2), ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♮
}

@[unfoldable] definition ObjectAsFunctor { C : Category } ( X : C.Obj ) : Functor (DiscreteCategory unit) C :=
{
  onObjects     := λ _, X,
  onMorphisms   := λ _ _ _, C.identity X,
  identities    := ♮,
  functoriality := ♮
}

@[unfoldable] definition SliceCategory   { C : Category } ( X : C.Obj ) := CommaCategory (IdentityFunctor C) (ObjectAsFunctor X)
@[unfoldable] definition CosliceCategory { C : Category } ( X : C.Obj ) := CommaCategory (ObjectAsFunctor X) (IdentityFunctor C)

-- In Cones, we have
--   A = C
--   B = .
--   C = FunctorCategory J C
@[unfoldable] definition Cones   { J C : Category } ( F : Functor J C ) := CommaCategory (DiagonalFunctor J C)                      (ObjectAsFunctor F)
@[unfoldable] definition Cocones { J C : Category } ( F : Functor J C ) := CommaCategory (@ObjectAsFunctor (FunctorCategory J C) F) (DiagonalFunctor J C)

@[unfoldable] definition Limit   { J C : Category } ( F: Functor J C ) := TerminalObject (Cones   F)
@[unfoldable] definition Colimit { J C : Category } ( F: Functor J C ) := InitialObject  (Cocones F)

inductive Two : Type
| _0 : Two
| _1 : Two

open Two

definition WalkingPair : Graph := {
  vertices := Two,
  edges    := λ X Y, empty
}
definition WalkingParallelPair : Graph := {
  vertices := Two,
  edges    := λ X Y, match X, Y with 
                       | _0, _1 := Two
                       | _,  _  := empty
                     end
}

definition Pair_homomorphism { C : Category } ( α β : C.Obj ) : GraphHomomorphism WalkingPair C := {
  onVertices := λ X, match X with
                       | _0 := α
                       | _1 := β
                    end,
  onEdges    := λ X Y e, match X, Y, e with end
}

definition ParallelPair_homomorphism { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) : GraphHomomorphism WalkingParallelPair C := {
  onVertices := λ X, match X with
                       | _0 := α
                       | _1 := β
                    end,
  onEdges    := λ X Y e, match X, Y, e with
                           | _0, _1, _0 := f
                           | _0, _1, _1 := g
                         end
}

definition Product { C : Category } ( α β : C.Obj ) := Limit (Functor.from_GraphHomomorphism (Pair_homomorphism α β))
definition Coproduct { C : Category } ( α β : C.Obj ) := Colimit (Functor.from_GraphHomomorphism (Pair_homomorphism α β))
definition Equalizer { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) := Limit (Functor.from_GraphHomomorphism (ParallelPair_homomorphism f g))
definition Coequalizer { C : Category } { α β : C.Obj } ( f g : C.Hom α β ) := Colimit (Functor.from_GraphHomomorphism (ParallelPair_homomorphism f g))

end tqft.categories.comma

