-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..discrete_category
import ..natural_transformation
import ..graph

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.graph

namespace tqft.categories.comma

structure InitialObject ( C : Category ) :=
  (object : C^.Obj)
  (morphisms : ∀ Y : C^.Obj, C^.Hom object Y)
  (uniqueness : ∀ Y : C^.Obj, ∀ f : C^.Hom object Y, f = morphisms Y)

attribute [ematch] InitialObject.uniqueness

instance InitialObject_coercion_to_object { C : Category } : has_coe (InitialObject C) (C^.Obj) :=
  { coe := InitialObject.object }

structure is_initial { C : Category } ( X : C^.Obj ) :=
  (morphism : ∀ Y : C^.Obj, C^.Hom X Y)
  (uniqueness :  ∀ Y : C^.Obj, ∀ f : C^.Hom X Y, f = morphism Y)

attribute [ematch] is_initial.uniqueness

lemma InitialObjects_have_only_the_identity_endomorphism { C : Category } ( X: InitialObject C ) ( f : C^.Hom X X ) : f = C^.identity X :=
  begin
   blast, -- TODO blast is not actually doing anything here; but perhaps later it will.
   rewrite X^.uniqueness X f,
   rewrite X^.uniqueness X (C^.identity X)
  end

lemma InitialObjects_are_unique { C : Category } ( X Y : InitialObject C ) : Isomorphism C X Y :=
  {
      morphism  := X^.morphisms Y,
      inverse   := Y^.morphisms X,
      witness_1 := begin apply InitialObjects_have_only_the_identity_endomorphism end,
      witness_2 := begin apply InitialObjects_have_only_the_identity_endomorphism end
  }

definition Opposite ( C : Category ) : Category :=
{
  Obj      := C^.Obj,
  Hom      := λ X Y, C^.Hom Y X,
  identity := C^.identity,
  compose  := λ X Y Z f g, C^.compose g f,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

-- Do we dare:
definition TerminalObject ( C : Category ) := InitialObject (Opposite C)

-- If not:
-- structure TerminalObject ( C : Category ) :=
--   (object : C^.Obj)
--   (morphisms : ∀ Y : C^.Obj, C^.Hom Y object)
--   (uniqueness : ∀ Y : C^.Obj, ∀ f : C^.Hom Y object, f = morphisms Y)

open tqft.categories.functor
open tqft.categories.natural_transformation

-- The diagonal functor sends X to the constant functor that sends everything to X.
definition DiagonalFunctor ( J C : Category ) : Functor C (FunctorCategory J C) :=
{
  onObjects     := λ X : C^.Obj, {
    onObjects     := λ _, X,
    onMorphisms   := λ _ _ _, C^.identity X,
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
  Obj      := Σ a : A^.Obj, Σ b : B^.Obj, C^.Hom (S a) (T b),
  Hom      := λ p q, { gh : (A^.Hom p.1 q.1) × (B^.Hom p.2.1 q.2.1) // C^.compose (S^.onMorphisms gh.1) q.2.2 = C^.compose p.2.2 (T^.onMorphisms gh.2) },
  identity := λ p, ⟨ (A^.identity p.1, B^.identity p.2.1), ♮ ⟩,
  compose  := λ p q r f g, ⟨ (A^.compose (val f).1 (val g).1, B^.compose (val f).2 (val g).2), ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♮
}

definition ObjectAsFunctor { C : Category } ( X : C^.Obj ) : Functor (DiscreteCategory unit) C :=
{
  onObjects     := λ _, X,
  onMorphisms   := λ _ _ _, C^.identity X,
  identities    := ♮,
  functoriality := ♮
}

definition SliceCategory   { C : Category } ( X : C^.Obj ) := CommaCategory (IdentityFunctor C) (ObjectAsFunctor X)
definition CosliceCategory { C : Category } ( X : C^.Obj ) := CommaCategory (ObjectAsFunctor X) (IdentityFunctor C)

definition Cones   { J C : Category } ( F : Functor J C ) := CommaCategory (DiagonalFunctor J C)                      (ObjectAsFunctor F)
definition Cocones { J C : Category } ( F : Functor J C ) := CommaCategory (@ObjectAsFunctor (FunctorCategory J C) F) (DiagonalFunctor J C)

definition Limit   { J C : Category } ( F: Functor J C ) := TerminalObject (Cones   F)
definition Colimit { J C : Category } ( F: Functor J C ) := InitialObject  (Cocones F)

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

definition Pair_homomorphism { C : Category } ( α β : C^.Obj ) : GraphHomomorphism WalkingPair C := {
  onVertices := λ X, match X with
                       | _0 := α
                       | _1 := β
                    end,
  onEdges    := λ X Y e, match X, Y, e with end
}

definition ParallelPair_homomorphism { C : Category } { α β : C^.Obj } ( f g : C^.Hom α β ) : GraphHomomorphism WalkingParallelPair C := {
  onVertices := λ X, match X with
                       | _0 := α
                       | _1 := β
                    end,
  onEdges    := λ X Y e, match X, Y, e with
                           | _0, _1, _0 := f
                           | _0, _1, _1 := g
                         end
}

definition Product { C : Category } ( α β : C^.Obj ) := Limit (Functor.from_GraphHomomorphism (Pair_homomorphism α β))
definition Coproduct { C : Category } ( α β : C^.Obj ) := Colimit (Functor.from_GraphHomomorphism (Pair_homomorphism α β))
definition Equalizer { C : Category } { α β : C^.Obj } ( f g : C^.Hom α β ) := Limit (Functor.from_GraphHomomorphism (ParallelPair_homomorphism f g))
definition Coequalizer { C : Category } { α β : C^.Obj } ( f g : C^.Hom α β ) := Colimit (Functor.from_GraphHomomorphism (ParallelPair_homomorphism f g))

end tqft.categories.comma

