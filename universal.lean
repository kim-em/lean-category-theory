-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .isomorphism
import .discrete_category
import .functor
import .natural_transformation
import .examples.types

open tqft.categories
open tqft.categories.isomorphism

namespace tqft.categories.universal

structure InitialObject ( C : Category ) :=
  (object : C^.Obj)
  (morphisms : ∀ Y : C^.Obj, C^.Hom object Y)
  (uniqueness : ∀ Y : C^.Obj, ∀ f : C^.Hom object Y, f = morphisms Y)

instance InitialObject_coercion_to_object { C : Category } : has_coe (InitialObject C) (C^.Obj) :=
  { coe := InitialObject.object }

structure is_initial { C : Category } ( X : C^.Obj ) :=
  (morphism : ∀ Y : C^.Obj, C^.Hom X Y)
  (uniqueness :  ∀ Y : C^.Obj, ∀ f : C^.Hom X Y, f = morphism Y)

attribute [ematch] is_initial.uniqueness

lemma InitialObjects_have_only_the_identity_endomorphism { C : Category } ( X: InitialObject C ) ( f : C^.Hom X X ) : f = C^.identity X :=
  begin
   blast, -- blast is not actually doing anything here; but perhaps later it will.
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
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

definition ObjectAsFunctor { C : Category } ( X : C^.Obj ) : Functor (DiscreteCategory unit) C :=
{
  onObjects     := λ _, X,
  onMorphisms   := λ _ _ _, C^.identity X,
  identities    := ♮,
  functoriality := ♮
}

-- PROJECT give the direct definition of slice and coslice categories, and then prove equivalence with this.
definition SliceCategory   { C : Category } ( X : C^.Obj ) := CommaCategory (IdentityFunctor C) (ObjectAsFunctor X)
definition CosliceCategory { C : Category } ( X : C^.Obj ) := CommaCategory (ObjectAsFunctor X) (IdentityFunctor C)

definition Cones   { J C : Category } ( F : Functor J C ) := CommaCategory (DiagonalFunctor J C)                      (ObjectAsFunctor F)
definition Cocones { J C : Category } ( F : Functor J C ) := CommaCategory (@ObjectAsFunctor (FunctorCategory J C) F) (DiagonalFunctor J C)

definition Limit   { J C : Category } ( F: Functor J C ) := TerminalObject (Cones   F)
definition Colimit { J C : Category } ( F: Functor J C ) := InitialObject  (Cocones F)

structure ExplicitCone { J C : Category } ( F: Functor J C ) :=
  ( limit : C^.Obj )
  ( maps  : Π X : J^.Obj, C^.Hom limit (F X) )
  ( commutativity : Π X Y : J^.Obj, Π f : J^.Hom X Y, C^.compose (maps X) (F^.onMorphisms f) = maps Y )

open tqft.categories.examples.types

-- PROJECT Give more straightforward definitions, and then show they agree.
-- definition Cone_agrees_with_ExplicitCone { J C : Category } ( F: Functor J C ) : Isomorphism CategoryOfTypes (Cones F)^.Obj (ExplicitCone F) := sorry
-- definition Cones_agrees_with_ExplicitCones { J C : Category } ( F: Functor J C ) : Isomorphism CategoryOfTypes (Cones F) (ExplicitCones F) := sorry

inductive Two : Type
| _0 : Two
| _1 : Two

open Two

-- definition Product { C : Category } ( A B : C^.Obj ) :=
--   @Limit (DiscreteCategory Two) C
--   {
--     onObjects     := λ X,
--                        match X with
--                          | _0 := A
--                          | _1  := B
--                        end,
--     onMorphisms   := λ X Y f,
--                        match X, Y, f with
--                          | _0, _0, _ := C^.identity A
--                          | _1, _1, _ := C^.identity B
--                        end,
--     identities    := begin
--                        intros,
--                        exact sorry -- TODO how do we expand out these definitions?
--                      end,
--     functoriality := sorry
-- }

-- PROJECT then products, equalizers, etc.
-- perhaps a good way to find out if these definitions are usable is to verify that products are products.

-- PROJECT ... how to handle dual notions without too much duplication?

end tqft.categories.universal

